//! Multi-POD partitioner: take a statement DAG, hand back the shortest
//! chain of PODs that fits it.
//!
//! Each POD holds a bounded contiguous slice of some topological order
//! of the DAG, subject to per-POD caps (resource sums, distinct
//! custom-predicate IDs, plus an input-tree budget for chain and
//! external imports). The final (output) POD additionally has to
//! republish every output-public statement. The partitioner picks both
//! an ordering and where to cut it, minimising the number of PODs.
//!
//! This is really two sub-problems:
//!
//! - **Picking an ordering**. Combinatorial: there's no realistic way
//!   to search every topological order. We sample a small set of
//!   candidates: one bin-packing ordering ([`kahn_bin_packing`]), the
//!   DFS-from-sinks ordering ([`build_dfs_topo_order`]), and ten
//!   random-priority orderings ([`kahn_with_priority`]).
//!
//! - **Cutting the ordering into segments**. Once the order is fixed
//!   this collapses to a 1D problem: where do POD boundaries go?
//!   Dynamic programming over prefixes solves it optimally in
//!   O(n * W^2) where W = `max_statements` (see [`run_dp`]). It
//!   also ensures feasibility in cases where a left-to-right greedy
//!   walk produces an infeasible partition; the per-ordering
//!   feasibility-rescue counts in [`ordering_and_cutter_contribution_sweep`]
//!   quantify how often this happens.

use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap, HashSet},
};

use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaCha20Rng;

use super::{
    cost::{CustomPredicateId, OperationCost, ResourceTotals},
    shape::{AbstractDep, InputShape, OutputShape},
};
use crate::middleware::Params;

/// Random-priority orderings generated as seed candidates.
const NUM_RANDOM_ORDERINGS: usize = 10;

/// Seed for the random-priority RNG. Fixed so candidate generation is
/// deterministic per input.
const RANDOM_SEED: u64 = 0x_C0FFEE_C0FFEE_u64;

/// Partition the input into a chain of PODs.
///
/// Returns `None` if no candidate ordering admits a finite-K partition;
/// the caller should invoke the diagnostic path for a structured error.
///
/// Every candidate ordering gets cut by [`run_dp`]; the lowest-K result
/// wins. We bail out as soon as some candidate hits the resource-induced
/// lower bound (no ordering can beat that), so the common case stays
/// cheap.
pub fn partition(input: &InputShape) -> Option<OutputShape> {
    let n = input.num_statements();
    if n == 0 {
        return Some(OutputShape {
            pod_count: 0,
            pod_statements: vec![],
            pod_republished_externals: vec![],
        });
    }
    if input.output_public_indices.len() > input.params.max_public_statements {
        return None;
    }

    let lower_bound = resource_lower_bound_k(input);
    let mut best: Option<OutputShape> = None;

    for ordering in candidate_orderings(input) {
        let Some(segments) = run_dp(&ordering, input) else {
            continue;
        };
        let k = segments.len();
        if best.as_ref().is_none_or(|b| k < b.pod_count) {
            best = Some(reconstruct(&ordering, &segments));
            if k <= lower_bound {
                break;
            }
        }
    }
    best
}

/// Estimated lower bound on K. Returns the largest per-resource
/// `ceil(total_r / cap_r)` across statement count, summable resources,
/// and distinct custom-predicate IDs; no partition can beat that. Used
/// by [`partition`] to early-exit ordering search once a candidate
/// matches.
///
/// This estimate is loose because it does not account for the maximum
/// number of imported statements per POD, which might result in a higher
/// K than the estimate.
fn resource_lower_bound_k(input: &InputShape) -> usize {
    ResourceTotals::accumulate(input.costs.iter()).min_pods(&input.params)
}

/// Produce a topological ordering biased to keep mutually-fittable
/// statements adjacent, so the DP cutter sees fewer infeasible
/// segments. Built greedily: maintain a running segment, admit ready
/// statements that fit within per-POD caps; when nothing fits, close
/// the segment and open a new one.
///
/// `tiebreak_priority` selects among multiple fitting ready statements;
/// `0..n` (identity) produces a deterministic source-order tiebreak.
pub(super) fn kahn_bin_packing(
    input: &InputShape,
    tiebreak_priority: &[usize],
) -> Option<Vec<usize>> {
    let n = input.num_statements();
    if n == 0 {
        return Some(Vec::new());
    }
    let params = &input.params;
    let (mut indegree, consumers) = input.indegree_and_consumers();
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    // While building each segment, the bin-packing fit check needs to
    // know how many statements in the segment are currently "exported"
    // (live consumers in a later segment, counted against
    // `max_public_statements`). We track that via `unfinished_consumers[d]`:
    // a per-statement countdown that decreases by one each time one of
    // d's consumers is admitted to a segment. When it hits zero, and d
    // isn't separately required by being output-public, d stops counting
    // against the publish cap.
    //
    // `consumers[d]` may list the same consumer twice if that consumer
    // has two `Internal(d)` entries in its dep_edges (e.g. an op whose
    // two arguments both reference d). The countdown is decremented once
    // per consumer admission, not once per dep edge, so we initialise it
    // from the distinct-consumer count.
    let distinct_consumer_count: Vec<usize> = consumers
        .iter()
        .map(|cs| {
            let set: BTreeSet<usize> = cs.iter().copied().collect();
            set.len()
        })
        .collect();
    let is_exporter: Vec<bool> = (0..n)
        .map(|s| distinct_consumer_count[s] > 0 || output_pub_set.contains(&s))
        .collect();
    let mut ordering: Vec<usize> = Vec::with_capacity(n);
    let mut pos_built = vec![usize::MAX; n];
    let mut state = GreedyState {
        unfinished_consumers: vec![0; n],
        ..GreedyState::default()
    };
    let mut ready: Vec<usize> = (0..n).filter(|&s| indegree[s] == 0).collect();

    // Tiebreak: prefer ready statements that already have deps in the
    // current segment, so dep-tight clusters admit contiguously instead
    // of being split by unrelated statements.
    fn coupling_score(deps: &[AbstractDep], pos_built: &[usize], segment_start: usize) -> usize {
        deps.iter()
            .filter(|d| match d {
                AbstractDep::Internal(d) => {
                    pos_built[*d] != usize::MAX && pos_built[*d] >= segment_start
                }
                _ => false,
            })
            .count()
    }

    while !ready.is_empty() {
        // If the segment is empty, pick by tiebreak alone; otherwise
        // prefer the lowest-tiebreak ready statement that fits, falling
        // back to lowest-tiebreak overall when nothing fits (which
        // closes the segment).
        let (chosen_idx, opens_new_segment) = if state.totals.num_operations == 0 {
            // Empty segment: no coupling signal yet, identity tiebreak only.
            let i = ready
                .iter()
                .enumerate()
                .min_by_key(|(_, &s)| tiebreak_priority[s])
                .expect("ready is non-empty")
                .0;
            (i, true)
        } else {
            let segment_start = state.a;
            let mut best_fit: Option<usize> = None;
            let mut best_fit_prio = (usize::MAX, usize::MAX);
            let mut best_overall = 0_usize;
            let mut best_overall_prio = (usize::MAX, usize::MAX);
            for (i, &s) in ready.iter().enumerate() {
                let coupling = coupling_score(&input.dep_edges[s], &pos_built, segment_start);
                let prio = (usize::MAX - coupling, tiebreak_priority[s]);
                if prio < best_overall_prio {
                    best_overall_prio = prio;
                    best_overall = i;
                }
                let cost = &input.costs[s];
                let deps = &input.dep_edges[s];
                if state
                    .can_extend(
                        cost,
                        deps,
                        &pos_built,
                        is_exporter[s],
                        &output_pub_set,
                        params,
                    )
                    .is_some()
                    && prio < best_fit_prio
                {
                    best_fit_prio = prio;
                    best_fit = Some(i);
                }
            }
            match best_fit {
                Some(i) => (i, false),
                None => (best_overall, true),
            }
        };

        let s = ready.swap_remove(chosen_idx);
        let cost = &input.costs[s];
        let deps = &input.dep_edges[s];
        if opens_new_segment {
            state.reset();
            state.a = ordering.len();
        }
        state.commit_extend(
            s,
            cost,
            deps,
            &pos_built,
            is_exporter[s],
            distinct_consumer_count[s],
            &output_pub_set,
        );
        pos_built[s] = ordering.len();
        ordering.push(s);
        for &c in &consumers[s] {
            indegree[c] -= 1;
            if indegree[c] == 0 {
                ready.push(c);
            }
        }
    }

    (ordering.len() == n).then_some(ordering)
}

/// Kahn topological sort with a per-statement priority. Statements with
/// lower priority values are picked first when multiple are ready.
pub(super) fn kahn_with_priority(input: &InputShape, prio_of: &[usize]) -> Option<Vec<usize>> {
    let n = input.num_statements();
    let (mut indegree, consumers) = input.indegree_and_consumers();

    let mut ordering = Vec::with_capacity(n);
    let mut ready: BinaryHeap<Reverse<(usize, usize)>> = (0..n)
        .filter(|&s| indegree[s] == 0)
        .map(|s| Reverse((prio_of[s], s)))
        .collect();
    while let Some(Reverse((_, s))) = ready.pop() {
        ordering.push(s);
        for &c in &consumers[s] {
            indegree[c] -= 1;
            if indegree[c] == 0 {
                ready.push(Reverse((prio_of[c], c)));
            }
        }
    }

    (ordering.len() == n).then_some(ordering)
}

/// Per-segment cap check for input-tree imports (chain slot + external
/// slots) and input-pods. Tree imports are capped by
/// `params.max_open_input_statement_ops`; the chain slot counts as one
/// input-pod iff there are any prev-pod producers.
fn tree_imports_ok(
    n_producers: usize,
    n_ext_imports: usize,
    n_ext_pods: usize,
    params: &Params,
) -> bool {
    n_producers + n_ext_imports <= params.max_open_input_statement_ops
        && usize::from(n_producers > 0) + n_ext_pods <= params.max_input_pods
}

/// Running state of the current segment used by greedy packing in
/// [`kahn_bin_packing`]. Scalar resource sums live in `totals`; the
/// remaining values track sets where we need to check for duplicates.
#[derive(Default)]
struct GreedyState {
    a: usize,
    totals: ResourceTotals,
    distinct_cps: Vec<CustomPredicateId>,
    prev_pod_producers: Vec<usize>,
    external_imports: Vec<usize>,
    external_pods: Vec<usize>,
    /// Statements admitted to the current segment that would land on
    /// the chain tree if the segment closed now (live consumers
    /// downstream of the segment, or output-public). Decreases as
    /// admissions finish off a producer's remaining consumers; see
    /// `unfinished_consumers` for the per-statement countdown.
    exported_count: usize,
    /// For each statement that has been admitted at any point, the
    /// number of distinct internal consumers not yet admitted to the
    /// current segment. Sized once at the top of `kahn_bin_packing`.
    /// `usize::MAX` for statements not yet admitted to any segment.
    /// On segment reset, entries for the previous segment's members
    /// are stale but irrelevant: the export check only looks at
    /// statements in the current segment, identified via `pos_built >=
    /// state.a`.
    unfinished_consumers: Vec<usize>,
    /// Scratch buffers used inside [`can_extend`] for deduplication.
    /// Cleared on each call to avoid churning allocations.
    scratch_new_producers: Vec<usize>,
    scratch_new_ext_imports: Vec<usize>,
    scratch_new_ext_pods: Vec<usize>,
    /// Scratch buffer for [`can_extend`]'s tentative export check:
    /// holds distinct in-segment dep targets of the candidate to avoid
    /// double-decrementing `unfinished_consumers` when a candidate
    /// names the same producer twice.
    scratch_seen_segment_deps: Vec<usize>,
}

impl GreedyState {
    fn reset(&mut self) {
        self.a = 0;
        self.totals = ResourceTotals::default();
        self.distinct_cps.clear();
        self.prev_pod_producers.clear();
        self.external_imports.clear();
        self.external_pods.clear();
        self.exported_count = 0;
        // Keep `unfinished_consumers`: prev-segment entries are stale
        // but the export check skips them anyway (gated by segment
        // membership), and future-segment members still hold their
        // initial total-consumer counts from setup.
    }

    /// Would the current segment still satisfy all per-POD caps after
    /// adding `cost` / `deps`? On success, returns the number of *new*
    /// import slots (chain + external) the admission would consume, used
    /// by the bin-packing tiebreak to prefer admissions that don't drag
    /// fresh imports into the segment. `None` means infeasible. Mutates
    /// only the `scratch_*` fields.
    fn can_extend(
        &mut self,
        cost: &OperationCost,
        deps: &[AbstractDep],
        pos_of: &[usize],
        is_exporter: bool,
        output_pub_set: &HashSet<usize>,
        params: &Params,
    ) -> Option<usize> {
        // Compute the candidate's net effect on the segment's export
        // count. Admitting the candidate may add one (if the candidate
        // itself has downstream consumers or is output-public) and may
        // subtract one for each in-segment producer it finishes off
        // (the producer drops out of the exported set since none of
        // its consumers sit downstream of the segment any more, unless
        // it's separately output-public). Reject if the net effect would
        // bust `max_public_statements`.
        let mut tentative_exports = self.exported_count;
        self.scratch_seen_segment_deps.clear();
        for dep in deps {
            if let AbstractDep::Internal(d) = dep {
                if pos_of[*d] != usize::MAX
                    && pos_of[*d] >= self.a
                    && !self.scratch_seen_segment_deps.contains(d)
                {
                    self.scratch_seen_segment_deps.push(*d);
                    if self.unfinished_consumers[*d] == 1 && !output_pub_set.contains(d) {
                        tentative_exports -= 1;
                    }
                }
            }
        }
        if is_exporter {
            tentative_exports += 1;
        }
        if tentative_exports > params.max_public_statements {
            return None;
        }
        let new_cp_count = cost
            .custom_predicates_ids
            .iter()
            .filter(|id| !self.distinct_cps.contains(id))
            .count();
        let mut tentative = self.totals.clone();
        tentative.add(cost);
        tentative.distinct_custom_predicates = self.distinct_cps.len() + new_cp_count;
        if !tentative.fits_in_pod(params) {
            return None;
        }

        self.scratch_new_producers.clear();
        self.scratch_new_ext_imports.clear();
        self.scratch_new_ext_pods.clear();
        for dep in deps {
            match dep {
                AbstractDep::Internal(d) => {
                    if pos_of[*d] < self.a
                        && !self.prev_pod_producers.contains(d)
                        && !self.scratch_new_producers.contains(d)
                    {
                        self.scratch_new_producers.push(*d);
                    }
                }
                AbstractDep::External { pod, statement } => {
                    if !self.external_imports.contains(statement)
                        && !self.scratch_new_ext_imports.contains(statement)
                    {
                        self.scratch_new_ext_imports.push(*statement);
                    }
                    if !self.external_pods.contains(pod) && !self.scratch_new_ext_pods.contains(pod)
                    {
                        self.scratch_new_ext_pods.push(*pod);
                    }
                }
            }
        }
        let n_producers = self.prev_pod_producers.len() + self.scratch_new_producers.len();
        let n_ext_imports = self.external_imports.len() + self.scratch_new_ext_imports.len();
        let n_ext_pods = self.external_pods.len() + self.scratch_new_ext_pods.len();
        if !tree_imports_ok(n_producers, n_ext_imports, n_ext_pods, params) {
            return None;
        }
        // Statement-table cap: local segment statements plus chain and
        // external imports together share `max_statements`, because each
        // `OpenInputStatement` op produces a statement in the POD's table.
        if tentative.num_operations + n_producers + n_ext_imports > params.max_statements {
            return None;
        }
        Some(self.scratch_new_producers.len() + self.scratch_new_ext_imports.len())
    }

    /// Apply the admission of `stmt` to the current segment: update
    /// resource totals, custom-predicate dedup, the export-tracking
    /// countdowns, and the input-tree import sets. The publish-cap
    /// impact must already have been verified by [`can_extend`].
    #[allow(clippy::too_many_arguments)]
    fn commit_extend(
        &mut self,
        stmt: usize,
        cost: &OperationCost,
        deps: &[AbstractDep],
        pos_of: &[usize],
        is_exporter: bool,
        distinct_consumer_count: usize,
        output_pub_set: &HashSet<usize>,
    ) {
        self.totals.add(cost);
        for id in &cost.custom_predicates_ids {
            if !self.distinct_cps.contains(id) {
                self.distinct_cps.push(id.clone());
            }
        }
        self.totals.distinct_custom_predicates = self.distinct_cps.len();
        // Commit the subtraction side of can_extend's tentative count:
        // each in-segment producer of `stmt` loses one unfinished consumer,
        // and any whose count hits zero drops out of the exported set
        // (unless it's separately output-public).
        self.scratch_seen_segment_deps.clear();
        for dep in deps {
            if let AbstractDep::Internal(d) = dep {
                if pos_of[*d] != usize::MAX
                    && pos_of[*d] >= self.a
                    && !self.scratch_seen_segment_deps.contains(d)
                {
                    self.scratch_seen_segment_deps.push(*d);
                    self.unfinished_consumers[*d] -= 1;
                    if self.unfinished_consumers[*d] == 0 && !output_pub_set.contains(d) {
                        self.exported_count -= 1;
                    }
                }
            }
        }
        // Set up stmt's own export-tracking entry: a fresh countdown of
        // its consumers (none admitted yet, since stmt itself was just
        // admitted) and a +1 to the exported set if stmt is itself an
        // exporter.
        self.unfinished_consumers[stmt] = distinct_consumer_count;
        if is_exporter {
            self.exported_count += 1;
        }
        for dep in deps {
            match dep {
                AbstractDep::Internal(d) => {
                    if pos_of[*d] < self.a && !self.prev_pod_producers.contains(d) {
                        self.prev_pod_producers.push(*d);
                    }
                }
                AbstractDep::External { pod, statement } => {
                    if !self.external_imports.contains(statement) {
                        self.external_imports.push(*statement);
                    }
                    if !self.external_pods.contains(pod) {
                        self.external_pods.push(*pod);
                    }
                }
            }
        }
    }
}

/// Reusable scratch for [`run_dp`]'s segment-feasibility checks.
#[derive(Default)]
struct DpWorkspace {
    /// Producers in earlier PODs that the current segment imports via
    /// the input tree's chain slot (statement indices).
    prev_pod_producers: HashSet<usize>,
    /// External (input) statements imported by the current segment.
    external_imports: HashSet<usize>,
    /// External pods referenced by the current segment.
    external_pods: HashSet<usize>,
    /// Linear-scan dedup buffer for custom-predicate identifiers used by
    /// statements in the segment. Cleared at the start of each check.
    distinct_cps: Vec<CustomPredicateId>,
}

fn random_priority(rng: &mut ChaCha20Rng, n: usize) -> Vec<usize> {
    let mut prio_of: Vec<usize> = (0..n).collect();
    prio_of.shuffle(rng);
    prio_of
}

/// Generate the candidate orderings the cutter will try. Bin-packing
/// goes first (strongest single seed on production-cap workloads),
/// then DFS-from-sinks, then the random-priority orderings for variety.
fn candidate_orderings(input: &InputShape) -> Vec<Vec<usize>> {
    let n = input.num_statements();
    let mut orderings: Vec<Vec<usize>> = Vec::new();

    let prio_id: Vec<usize> = (0..n).collect();
    if let Some(o) = kahn_bin_packing(input, &prio_id) {
        orderings.push(o);
    }

    orderings.push(build_dfs_topo_order(input));

    let mut rng = ChaCha20Rng::seed_from_u64(RANDOM_SEED);
    for _ in 0..NUM_RANDOM_ORDERINGS {
        let prio = random_priority(&mut rng, n);
        if let Some(o) = kahn_with_priority(input, &prio) {
            orderings.push(o);
        }
    }

    orderings
}

/// Maps statements to their position in an ordering.
fn build_pos_in_ordering(ordering: &[usize]) -> Vec<usize> {
    let n = ordering.len();
    let mut pos = vec![usize::MAX; n];
    for (i, &s) in ordering.iter().enumerate() {
        pos[s] = i;
    }
    pos
}

/// Topological ordering that keeps each statement's dep-closure
/// contiguous immediately before it. For workloads with
/// definition-then-distant-use patterns this shortens producer-
/// consumer index gaps versus the canonical user-input order, so the
/// segment cutter can admit a definition-and-use cluster as one
/// segment. Built by depth-first search from sinks (statements with
/// no internal consumers), recursing into deps before emitting each
/// statement.
pub(super) fn build_dfs_topo_order(input: &InputShape) -> Vec<usize> {
    let n = input.num_statements();
    let mut has_consumer = vec![false; n];
    for deps in &input.dep_edges {
        for dep in deps {
            if let AbstractDep::Internal(d) = dep {
                has_consumer[*d] = true;
            }
        }
    }
    let mut visited = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    for s in 0..n {
        if !has_consumer[s] && !visited[s] {
            dfs_emit(s, input, &mut visited, &mut order);
        }
    }
    // Cover anything unreachable from a sink (e.g. orphan sub-DAGs).
    for s in 0..n {
        if !visited[s] {
            dfs_emit(s, input, &mut visited, &mut order);
        }
    }
    order
}

fn dfs_emit(s: usize, input: &InputShape, visited: &mut [bool], order: &mut Vec<usize>) {
    if visited[s] {
        return;
    }
    visited[s] = true;
    for dep in &input.dep_edges[s] {
        if let AbstractDep::Internal(d) = *dep {
            dfs_emit(d, input, visited, order);
        }
    }
    order.push(s);
}

/// Per-statement max-consumer-position lookup against an ordering.
/// `max_consumer_pos[s]` is the largest position in `ordering` of any
/// statement that has `s` as an `Internal` dep, or 0 if `s` has no
/// internal consumers.
fn build_max_consumer_pos(consumers: &[Vec<usize>], pos_in_ordering: &[usize]) -> Vec<usize> {
    let n = consumers.len();
    let mut mcp = vec![0_usize; n];
    for (d, cs) in consumers.iter().enumerate() {
        for &c in cs {
            if pos_in_ordering[c] > mcp[d] {
                mcp[d] = pos_in_ordering[c];
            }
        }
    }
    mcp
}

/// Non-terminal-only per-segment feasibility check, self-contained
/// (builds its own `pos_in_ordering` and `DpWorkspace`). Callers in a
/// hot loop should use `segment_feasible_with` to reuse allocations.
pub(super) fn segment_feasible(ordering: &[usize], input: &InputShape, a: usize, p: usize) -> bool {
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    let mut ws = DpWorkspace::default();
    segment_feasible_with(
        ordering,
        &pos_in_ordering,
        &max_consumer_pos,
        &output_pub_set,
        input,
        a,
        p,
        false,
        &mut ws,
    )
}

/// Greedy partition of `ordering` into segments: extend each segment
/// as long as feasibility holds, close at the first cap-bust. With
/// `check_terminal`, additionally verifies that the final segment is
/// feasible as the output POD; without, returns the non-terminal
/// segmentation only.
///
/// Returns `None` if any single statement is infeasible as a 1-stmt
/// segment, or (when `check_terminal`) if the trailing segment fails
/// terminal availability.
#[cfg(test)]
fn greedy_segments(
    ordering: &[usize],
    input: &InputShape,
    check_terminal: bool,
) -> Option<Vec<Segment>> {
    let n = ordering.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    let mut ws = DpWorkspace::default();
    let mut segments: Vec<Segment> = Vec::new();
    let mut start = 0_usize;
    while start < n {
        if !segment_feasible_with(
            ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            start,
            start + 1,
            false,
            &mut ws,
        ) {
            return None;
        }
        let mut end = start + 1;
        while end < n
            && segment_feasible_with(
                ordering,
                &pos_in_ordering,
                &max_consumer_pos,
                &output_pub_set,
                input,
                start,
                end + 1,
                false,
                &mut ws,
            )
        {
            end += 1;
        }
        segments.push(Segment { start, end });
        start = end;
    }
    if check_terminal {
        let last = *segments
            .last()
            .expect("non-empty ordering produced no segments");
        if !segment_feasible_with(
            ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            last.start,
            last.end,
            true,
            &mut ws,
        ) {
            return None;
        }
    }
    Some(segments)
}

/// Number of segments a left-to-right greedy walk produces on the
/// given ordering, ignoring terminal-segment feasibility. Useful for
/// measuring how much the DP cutter improves on a greedy cut of the
/// same ordering.
#[cfg(test)]
pub(super) fn simulate_greedy_k(input: &InputShape, ordering: &[usize]) -> Option<usize> {
    greedy_segments(ordering, input, false).map(|s| s.len())
}

/// Workspace-backed feasibility check. Returns true iff segment
/// `ordering[start..end]` fits in one POD; `is_terminal` additionally
/// enforces output-POD availability for output-public statements
/// upstream of `start`.
///
/// Reuses `workspace` for the membership sets and the distinct-CP dedup
/// buffer; both are reset per call but their underlying allocations are
/// shared across the ~28K calls in one `run_dp`.
#[allow(clippy::too_many_arguments)]
fn segment_feasible_with(
    ordering: &[usize],
    pos_in_ordering: &[usize],
    max_consumer_pos: &[usize],
    output_pub_set: &HashSet<usize>,
    input: &InputShape,
    start: usize,
    end: usize,
    is_terminal: bool,
    workspace: &mut DpWorkspace,
) -> bool {
    let params = &input.params;
    let segment = &ordering[start..end];
    if segment.is_empty() || segment.len() > params.max_statements {
        return false;
    }

    // Single pass: per-statement, accumulate scalar sums + distinct CPs
    // (cap-checked via [`ResourceTotals::fits_in_pod`]) and record
    // input-tree imports. Input-tree imports come in two flavours, both
    // capped together by `max_open_input_statements` because the POD
    // circuit reads them through the same input-tree slots:
    // - prev-pod producers: statements produced in `[0..start)` (slot 0,
    //   the chain slot connecting this POD to its predecessor).
    // - external imports: external (input) statements (slots 1..N).
    // External-pod references are tracked separately for `max_input_pods`,
    // which is a per-slot cap, not a per-statement one.
    let mut totals = ResourceTotals::default();
    workspace.distinct_cps.clear();
    workspace.prev_pod_producers.clear();
    workspace.external_imports.clear();
    workspace.external_pods.clear();
    for &s in segment {
        let cost = &input.costs[s];
        totals.add(cost);
        for id in &cost.custom_predicates_ids {
            if !workspace.distinct_cps.contains(id) {
                workspace.distinct_cps.push(id.clone());
            }
        }
        totals.distinct_custom_predicates = workspace.distinct_cps.len();
        if !totals.fits_in_pod(params) {
            return false;
        }
        for dep in &input.dep_edges[s] {
            match dep {
                AbstractDep::Internal(d) => {
                    if pos_in_ordering[*d] < start {
                        workspace.prev_pod_producers.insert(*d);
                    }
                }
                AbstractDep::External { pod, statement } => {
                    workspace.external_imports.insert(*statement);
                    workspace.external_pods.insert(*pod);
                }
            }
        }
        // Mid-loop bail: the chain-slot + external-slot tree-imports
        // cap can only grow as we add more statements, so once it's
        // busted there's no recovery. Saves the remaining statements'
        // worth of inserts on infeasible segments.
        if workspace.prev_pod_producers.len() + workspace.external_imports.len()
            > params.max_open_input_statement_ops
        {
            return false;
        }
    }

    let n_ext_imports = workspace.external_imports.len();
    let n_ext_pods = workspace.external_pods.len();
    let n_chain_imports = workspace.prev_pod_producers.len();

    // Statement-table cap. Each `OpenInputStatement` op produces a statement
    // in the POD's statement table, so the table holds `segment statements +
    // imports`, capped by `max_statements`.
    if segment.len() + n_chain_imports + n_ext_imports > params.max_statements {
        return false;
    }

    if !tree_imports_ok(n_chain_imports, n_ext_imports, n_ext_pods, params) {
        return false;
    }

    if !is_terminal {
        // Publish cap: each statement in the segment that has a consumer
        // at or beyond `end`, or that is an output-public (the terminal
        // POD pulls it from the chain), occupies one slot on the chain
        // tree this POD appends to. The terminal POD doesn't extend the
        // chain: its fresh-tree size is `|output_public_indices|`,
        // pre-checked by callers before invoking the partitioner.
        let mut exports = 0_usize;
        for &s in segment {
            if max_consumer_pos[s] >= end || output_pub_set.contains(&s) {
                exports += 1;
            }
        }
        return exports <= params.max_public_statements;
    }

    // Terminal: output_public statements in the prefix become additional
    // prev-pod producers (the output POD must republish them on its
    // fresh tree).
    for &out_pub in &input.output_public_indices {
        if pos_in_ordering[out_pub] < start {
            workspace.prev_pod_producers.insert(out_pub);
        }
    }
    let n_chain_imports_terminal = workspace.prev_pod_producers.len();
    if segment.len() + n_chain_imports_terminal + n_ext_imports > params.max_statements {
        return false;
    }
    tree_imports_ok(n_chain_imports_terminal, n_ext_imports, n_ext_pods, params)
}

/// A half-open boundary range covering one POD's statements:
/// `ordering[start..end]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Segment {
    start: usize,
    end: usize,
}

/// Which flavour of feasibility rules applies to a candidate segment:
/// the chain-extending rules used for every POD except the last, or
/// the output-POD rules (fresh public tree, must republish upstream
/// output-publics).
#[derive(Clone, Copy)]
enum PodKind {
    ChainExtending,
    Output,
}

impl PodKind {
    fn is_terminal(self) -> bool {
        matches!(self, PodKind::Output)
    }
}

/// One row of the `dp` table. The cell at index `end` answers a
/// hypothetical question: "if we cut right here at boundary `end`,
/// what's the cheapest way to partition statements `0..end` into
/// chain-extending PODs?" `pod_count` is the answer (how many PODs);
/// `prev_start` is where the most recent POD in that cheapest
/// partition started.
///
/// `prev_start` is purely a breadcrumb. The forward sweep only needs
/// `pod_count` to compute later cells. We store `prev_start` so that,
/// once the sweep finishes, we can walk backwards through cells to
/// recover the actual cut positions.
#[derive(Clone, Copy)]
struct DpEntry {
    pod_count: usize,
    prev_start: usize,
}

/// Cut `ordering` into the fewest feasible PODs under per-POD caps.
/// Returns the cut list as a `Vec<Segment>` (one entry per POD, in
/// chain order), or `None` if no valid partition exists for this
/// ordering.
///
/// Picture the statements laid out in a row. Around them sit `n + 1`
/// boundary positions: 0 (before the first statement), 1 (between the
/// first and second), ..., `n` (after the last). Choosing how to
/// group statements into PODs is just choosing which boundaries to
/// use as cuts - the run of statements between consecutive cuts is
/// one POD. We want the fewest cuts possible while keeping every
/// resulting POD feasible under all the per-POD caps.
///
/// We fill a table `dp` left to right, one cell per boundary. The
/// cell at index `end` records the cheapest answer to "if we cut at
/// boundary `end`, how few PODs cover statements `0..end`?" To
/// compute it, we try every possible start for the last POD in the
/// window `end - max_segment_len .. end`, check feasibility of that
/// segment, and combine with the already-filled cell at `start`. The
/// minimum over all feasible starts becomes the cell at `end`. We
/// also remember which `start` won, so we can reconstruct the cuts
/// later.
///
/// This is just function evaluation in a smart order, not a search.
/// We never commit to "POD 0 ends here" up front. We just record,
/// for every boundary, what the cheapest answer would be if a cut
/// landed there. The actual cuts fall out only at the very end, by
/// following breadcrumbs.
///
/// The last POD in the final chain has different feasibility rules
/// than the rest: it publishes a fresh tree of public statements
/// instead of extending the chain tree, and it may need to republish
/// output-public statements that landed in earlier PODs. So the main
/// sweep treats every segment as a chain-extending POD, and we do one
/// extra scan at the end over candidate output-POD starts to pick the
/// best one. That scan plus the breadcrumb chain back through `dp`
/// gives the full cut list.
///
/// If the output-POD scan finds no feasible start, this ordering has
/// no valid partition under the caps -- return `None` so the outer
/// search can try a different ordering.
#[allow(clippy::needless_range_loop)]
fn run_dp(ordering: &[usize], input: &InputShape) -> Option<Vec<Segment>> {
    let n = ordering.len();
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    // Each POD holds at most `max_statements` local statements, so any
    // candidate segment longer than that is infeasible. This bounds
    // the inner loop's start window per `end`.
    let max_segment_len = input.params.max_statements;

    // The table has `n + 1` cells, one per boundary position (including
    // 0 and n). `dp[0]` is the base case: the empty prefix needs 0 PODs.
    let mut dp: Vec<Option<DpEntry>> = vec![None; n + 1];
    let mut workspace = DpWorkspace::default();
    dp[0] = Some(DpEntry {
        pod_count: 0,
        prev_start: 0,
    });

    // Compute one cell: try every feasible start for a POD ending at
    // `end`, return the cheapest combination (or None if none fit).
    // Used twice below: once per cell during the forward sweep, and
    // once more for the output POD's terminal scan.
    let best_segment_ending_at = |end: usize,
                                  kind: PodKind,
                                  dp: &[Option<DpEntry>],
                                  workspace: &mut DpWorkspace|
     -> Option<DpEntry> {
        let window_start = end.saturating_sub(max_segment_len);
        let mut best: Option<DpEntry> = None;
        for start in window_start..end {
            let Some(prev) = dp[start] else { continue };
            if !segment_feasible_with(
                ordering,
                &pos_in_ordering,
                &max_consumer_pos,
                &output_pub_set,
                input,
                start,
                end,
                kind.is_terminal(),
                workspace,
            ) {
                continue;
            }
            let candidate = DpEntry {
                pod_count: prev.pod_count + 1,
                prev_start: start,
            };
            if best.is_none_or(|b| candidate.pod_count < b.pod_count) {
                best = Some(candidate);
            }
        }
        best
    };

    // Forward sweep: fill cells left to right, treating every segment
    // as a chain-extending POD (the output POD's special rules are
    // handled separately below).
    for end in 1..=n {
        let entry = best_segment_ending_at(end, PodKind::ChainExtending, &dp, &mut workspace);
        dp[end] = entry;
    }

    // Terminal scan: pick the cheapest output POD covering `start..n`,
    // using the output-POD feasibility flavour. Returns `None` if no
    // candidate is feasible.
    let terminal = best_segment_ending_at(n, PodKind::Output, &dp, &mut workspace)?;

    // Backtrack: walk `prev_start` breadcrumbs from `terminal` back to
    // boundary 0 to recover the actual cut positions.
    Some(backtrack_segments(&dp, terminal, n))
}

/// Reconstruct the cut list by following `prev_start` breadcrumbs.
///
/// Each cell `dp[k]` recorded "the most recent POD in my cheapest
/// partition started at `prev_start`." Starting from the terminal
/// segment and hopping back along those pointers visits one cell per
/// POD, in reverse chain order. Reversing the collected `Segment`s
/// gives the final cut list in chain order.
///
/// This walk doesn't search or revise anything; every cell along the
/// path is already final from the forward sweep.
fn backtrack_segments(dp: &[Option<DpEntry>], terminal: DpEntry, n: usize) -> Vec<Segment> {
    let mut cursor = terminal.prev_start;
    let mut segments = vec![Segment {
        start: terminal.prev_start,
        end: n,
    }];
    while cursor > 0 {
        let entry = dp[cursor].expect("dp reachability already established");
        segments.push(Segment {
            start: entry.prev_start,
            end: cursor,
        });
        cursor = entry.prev_start;
    }
    segments.reverse();
    segments
}

/// Cut a single externally-supplied topological ordering into PODs.
/// Returns `None` only when a per-statement cap is itself violated: the
/// cutter is optimal over its given ordering, so any other failure mode
/// would mean that ordering simply has no valid partition. Used by
/// tests that want to compare the partitioner's output against an
/// oracle-derived ordering.
#[cfg(test)]
pub(super) fn partition_with_ordering(
    input: &InputShape,
    ordering: &[usize],
) -> Option<OutputShape> {
    let segments = run_dp(ordering, input)?;
    Some(reconstruct(ordering, &segments))
}

fn reconstruct(ordering: &[usize], segments: &[Segment]) -> OutputShape {
    let pod_count = segments.len();
    let pod_statements: Vec<Vec<usize>> = segments
        .iter()
        .map(|seg| {
            let mut stmts: Vec<usize> = ordering[seg.start..seg.end].to_vec();
            stmts.sort_unstable();
            stmts
        })
        .collect();
    OutputShape {
        pod_count,
        pod_statements,
        pod_republished_externals: vec![BTreeSet::new(); pod_count],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::middleware::Params;

    fn empty_input() -> InputShape {
        InputShape {
            costs: vec![],
            dep_edges: vec![],
            output_public_indices: vec![],
            num_external_pods: 0,
            statement_pod: vec![],
            params: Params::default(),
        }
    }

    /// `n` independent statements with default cost and no deps. Useful for
    /// driving the partitioner with no dependency structure.
    fn independent_statements(n: usize, output_public: Vec<usize>, params: Params) -> InputShape {
        use super::super::cost::OperationCost;
        InputShape {
            costs: (0..n).map(|_| OperationCost::default()).collect(),
            dep_edges: (0..n).map(|_| Vec::new()).collect(),
            output_public_indices: output_public,
            num_external_pods: 0,
            statement_pod: vec![],
            params,
        }
    }

    #[test]
    fn empty_input_yields_zero_pods() {
        let out = partition(&empty_input()).expect("empty input should solve trivially");
        assert_eq!(out.pod_count, 0);
        assert!(out.pod_statements.is_empty());
    }

    #[test]
    fn single_pod_fits_when_caps_allow() {
        let input = independent_statements(3, vec![0, 1, 2], Params::default());
        let out = partition(&input).expect("should partition into a single POD");
        assert_eq!(out.pod_count, 1);
        assert_eq!(out.pod_statements[0], vec![0, 1, 2]);
    }

    #[test]
    fn splits_when_statement_count_exceeds_cap() {
        // Force a 2-POD split via tight max_statements.
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        // max_statements = 2; 3 statements need 2 PODs.
        let input = independent_statements(3, vec![2], params);
        let out = partition(&input).expect("should partition");
        assert_eq!(out.pod_count, 2);
        // Every statement should be assigned exactly once.
        let mut all: Vec<usize> = out.pod_statements.iter().flatten().copied().collect();
        all.sort();
        assert_eq!(all, vec![0, 1, 2]);
        // Statement 2 (output-public) must be in the terminal POD or
        // importable from upstream.
        let terminal_or_prefix =
            out.pod_statements[1].contains(&2) || out.pod_statements[0].contains(&2);
        assert!(terminal_or_prefix);
    }

    #[test]
    fn external_imports_count_against_max_open_input_statements() {
        // n statements, each with one External dep to a distinct input
        // statement from a single external POD. With one external pod,
        // `max_input_pods` can't force a split, so the only constraint
        // that drives K > 1 is the combined import cap.
        use super::super::cost::OperationCost;
        let params = Params::default();
        let n = params.max_open_input_statement_ops + 1;
        let input = InputShape {
            costs: (0..n).map(|_| OperationCost::default()).collect(),
            dep_edges: (0..n)
                .map(|i| {
                    vec![AbstractDep::External {
                        pod: 0,
                        statement: i,
                    }]
                })
                .collect(),
            output_public_indices: vec![0],
            num_external_pods: 1,
            statement_pod: vec![0; n],
            params,
        };
        let out = partition(&input).expect("should partition");
        assert!(
            out.pod_count >= 2,
            "external imports must count against max_open_input_statements, but {} \
             external imports packed into a single POD",
            n
        );
    }

    #[test]
    fn dependency_chain_respects_topo_order() {
        // 4 statements where each depends on the previous. With
        // max_statements = 3, a 2-POD partition is feasible: one POD
        // holds [0,1] (2 stmts, 0 imports) and the other [2,3] (2
        // stmts + 1 chain import of stmt 1 = 3 stmts at cap).
        use super::super::cost::OperationCost;
        let params = Params {
            max_statements: 3,
            ..Params::default()
        };
        let input = InputShape {
            costs: (0..4).map(|_| OperationCost::default()).collect(),
            dep_edges: vec![
                vec![],
                vec![AbstractDep::Internal(0)],
                vec![AbstractDep::Internal(1)],
                vec![AbstractDep::Internal(2)],
            ],
            output_public_indices: vec![3],
            num_external_pods: 0,
            statement_pod: vec![],
            params,
        };
        let out = partition(&input).expect("should partition");
        assert_eq!(out.pod_count, 2);
        // Every statement is placed exactly once and topo order is preserved.
        let mut all: Vec<usize> = out.pod_statements.iter().flatten().copied().collect();
        all.sort();
        assert_eq!(all, vec![0, 1, 2, 3]);
    }

    /// Per-input grid of K under each (ordering tier, cutter) pair.
    /// Scores each of the three ordering tiers (BP, DFS, random) under
    /// each of the two cutters (DP, greedy), then derives the per-tier
    /// contribution counts. The random row aggregates min-over-N over
    /// the N random orderings used by production, matching how the
    /// tier is consumed; bp and dfs are single-ordering tiers.
    ///
    /// Asserts that greedy never strictly beats DP on the *same*
    /// individual ordering; that check fires inside the random loop
    /// per ordering as well, separately from the min-of-N aggregation
    /// reported below.
    ///
    /// Shares its RNG seed and parameter variants with the DP-vs-MILP
    /// parity sweep so the two sweeps probe the same distribution.
    #[test]
    fn ordering_and_cutter_contribution_sweep() {
        use std::collections::BTreeMap;

        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;

        use super::super::partition_milp::random_input;

        let param_variants: Vec<(&str, Params)> = vec![
            (
                "tight",
                Params {
                    max_statements: 3,
                    max_input_pods: 2,
                    ..Params::default()
                },
            ),
            (
                "medium",
                Params {
                    max_statements: 5,
                    max_input_pods: 3,
                    ..Params::default()
                },
            ),
            (
                "resource-pressure",
                Params {
                    max_statements: 8,
                    max_input_pods: 3,
                    max_signed_by_ops: 2,
                    ..Params::default()
                },
            ),
        ];
        let n_values: Vec<usize> = vec![8, 12, 16, 24, 32];
        let trials_per_combo: usize = 25;

        #[derive(Default)]
        struct CellStats {
            feas: usize,
            k_sum: usize,
            k_max: usize,
        }
        impl CellStats {
            fn record(&mut self, k: Option<usize>) {
                if let Some(k) = k {
                    self.feas += 1;
                    self.k_sum += k;
                    if k > self.k_max {
                        self.k_max = k;
                    }
                }
            }
        }

        const ORDERINGS: [&str; 3] = ["bp", "dfs", "random"];
        const CUTTERS: [&str; 2] = ["dp", "greedy"];

        let mut cells: BTreeMap<(&str, &str), CellStats> = BTreeMap::new();
        let mut dp_beats_greedy: BTreeMap<&str, usize> = BTreeMap::new();
        let mut dp_rescues_greedy: BTreeMap<&str, usize> = BTreeMap::new();
        let mut k_rescues: BTreeMap<&str, usize> = BTreeMap::new();
        let mut feas_rescues: BTreeMap<&str, usize> = BTreeMap::new();

        let mut total: usize = 0;
        let mut rng = ChaCha20Rng::seed_from_u64(0xDEADBEEF);

        for (label, params) in &param_variants {
            for &n in &n_values {
                for trial in 0..trials_per_combo {
                    total += 1;
                    let input = random_input(&mut rng, n, params.clone());
                    let identity: Vec<usize> = (0..input.num_statements()).collect();

                    let k_per_ord_dp = |o: &[usize]| -> Option<usize> {
                        partition_with_ordering(&input, o).map(|s| s.pod_count)
                    };
                    let k_per_ord_greedy = |o: &[usize]| -> Option<usize> {
                        greedy_segments(o, &input, true).map(|s| s.len())
                    };

                    // Per-individual-ordering correctness invariant: greedy
                    // never strictly beats DP on the same ordering, and DP
                    // is always feasible where greedy is. Checked here so
                    // the random tier's individual orderings are tested
                    // separately from the min-of-N aggregation used in the
                    // contribution stats below.
                    let check_invariant =
                        |ord: &str, k_dp: Option<usize>, k_gr: Option<usize>, suffix: &str| match (
                            k_dp, k_gr,
                        ) {
                            (Some(d), Some(g)) => assert!(
                                d <= g,
                                "greedy strictly beat DP on {}{} [{} n={} trial={}] \
                                 (greedy={}, dp={})",
                                ord,
                                suffix,
                                label,
                                n,
                                trial,
                                g,
                                d,
                            ),
                            (None, Some(_)) => unreachable!(
                                "greedy feasible but DP infeasible on {}{} [{} n={} trial={}]: \
                                 DP considers greedy's cuts as a subset of its choices",
                                ord, suffix, label, n, trial,
                            ),
                            _ => {}
                        };

                    let bp_ord = kahn_bin_packing(&input, &identity);
                    let dfs_ord = build_dfs_topo_order(&input);
                    let k_bp_dp = bp_ord.as_deref().and_then(k_per_ord_dp);
                    let k_bp_gr = bp_ord.as_deref().and_then(k_per_ord_greedy);
                    let k_dfs_dp = k_per_ord_dp(&dfs_ord);
                    let k_dfs_gr = k_per_ord_greedy(&dfs_ord);
                    check_invariant("bp", k_bp_dp, k_bp_gr, "");
                    check_invariant("dfs", k_dfs_dp, k_dfs_gr, "");

                    let mut k_rnd_dp: Option<usize> = None;
                    let mut k_rnd_gr: Option<usize> = None;
                    let mut rprng = ChaCha20Rng::seed_from_u64(RANDOM_SEED);
                    for i in 0..NUM_RANDOM_ORDERINGS {
                        let prio = random_priority(&mut rprng, input.num_statements());
                        let Some(o) = kahn_with_priority(&input, &prio) else {
                            continue;
                        };
                        let k_dp = k_per_ord_dp(&o);
                        let k_gr = k_per_ord_greedy(&o);
                        check_invariant("random", k_dp, k_gr, &format!(" #{}", i));
                        if let Some(k) = k_dp {
                            k_rnd_dp = Some(k_rnd_dp.map_or(k, |cur| cur.min(k)));
                        }
                        if let Some(k) = k_gr {
                            k_rnd_gr = Some(k_rnd_gr.map_or(k, |cur| cur.min(k)));
                        }
                    }

                    // Tier-level contribution stats. For the random tier
                    // these aggregate min-over-N orderings, matching how
                    // production consumes the tier; for bp/dfs each tier
                    // is a single ordering. Per-individual-ordering
                    // correctness is already asserted above.
                    let row = [
                        ("bp", k_bp_dp, k_bp_gr),
                        ("dfs", k_dfs_dp, k_dfs_gr),
                        ("random", k_rnd_dp, k_rnd_gr),
                    ];
                    for &(ord, k_dp, k_gr) in &row {
                        cells.entry((ord, "dp")).or_default().record(k_dp);
                        cells.entry((ord, "greedy")).or_default().record(k_gr);
                        match (k_dp, k_gr) {
                            (Some(d), Some(g)) if d < g => {
                                *dp_beats_greedy.entry(ord).or_default() += 1;
                            }
                            (Some(_), None) => {
                                *dp_rescues_greedy.entry(ord).or_default() += 1;
                            }
                            _ => {}
                        }
                    }

                    let dp_ks = [("bp", k_bp_dp), ("dfs", k_dfs_dp), ("random", k_rnd_dp)];
                    for &(this_ord, this_k) in &dp_ks {
                        let others_min = dp_ks
                            .iter()
                            .filter(|(o, _)| *o != this_ord)
                            .filter_map(|(_, k)| *k)
                            .min();
                        match (this_k, others_min) {
                            (Some(t), Some(o)) if t < o => {
                                *k_rescues.entry(this_ord).or_default() += 1;
                            }
                            (Some(_), None) => {
                                *feas_rescues.entry(this_ord).or_default() += 1;
                            }
                            _ => {}
                        }
                    }
                }
            }
        }

        eprintln!();
        eprintln!(
            "=== Ordering tier x Cutter contribution sweep (inputs={}) ===",
            total
        );
        eprintln!();
        eprintln!(
            "Per-tier K stats (random row = best of {} orderings per input):",
            NUM_RANDOM_ORDERINGS
        );
        eprintln!(
            "  {:<8} {:<8} {:>5}  {:>7}  {:>6}",
            "tier", "cutter", "feas", "mean K", "max K"
        );
        for ord in &ORDERINGS {
            for cut in &CUTTERS {
                let (feas, k_sum, k_max) = cells
                    .get(&(*ord, *cut))
                    .map_or((0, 0, 0), |c| (c.feas, c.k_sum, c.k_max));
                let mean = if feas == 0 {
                    0.0
                } else {
                    k_sum as f64 / feas as f64
                };
                eprintln!(
                    "  {:<8} {:<8} {:>5}  {:>7.2}  {:>6}",
                    ord, cut, feas, mean, k_max
                );
            }
        }
        eprintln!();
        eprintln!(
            "DP vs greedy on the same tier (random = best of {}):",
            NUM_RANDOM_ORDERINGS
        );
        for ord in &ORDERINGS {
            eprintln!(
                "  {:<8} DP<greedy on {} inputs;  DP feasible / greedy infeasible on {}",
                ord,
                dp_beats_greedy.get(*ord).copied().unwrap_or(0),
                dp_rescues_greedy.get(*ord).copied().unwrap_or(0),
            );
        }
        eprintln!();
        eprintln!("Per-tier rescue against the other two (DP cuts):");
        for ord in &ORDERINGS {
            eprintln!(
                "  {:<8} K_rescue={} feasibility_rescue={}",
                ord,
                k_rescues.get(*ord).copied().unwrap_or(0),
                feas_rescues.get(*ord).copied().unwrap_or(0),
            );
        }
    }
}
