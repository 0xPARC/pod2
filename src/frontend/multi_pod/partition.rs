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
//!   candidates: one bin-packing ordering ([`kahn_bin_packing`]) and
//!   ten random-priority orderings ([`kahn_with_priority`]).
//!
//! - **Cutting the ordering into segments**. Once the order is fixed
//!   this collapses to a 1D problem: where do POD boundaries go?
//!   Dynamic programming over prefixes solves it optimally in
//!   O(n * W^2) where W = `max_priv_statements` (see [`run_dp`]). It
//!   also ensures feasibility in cases where a left-to-right greedy
//!   walk produces an infeasible partition; the DP-vs-greedy random
//!   sweep ([`dp_vs_greedy_random_sweep`]) measures how often this
//!   actually rescues a partition.

use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap, HashSet},
};

use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaCha20Rng;

use super::{
    cost::{CustomPredicateId, ResourceTotals, StatementCost},
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
    best.map(|out| refine_via_merges(input, out))
}

/// Post-process refinement: repeatedly try to merge adjacent PODs in
/// the chain. A merge of POD `p` and POD `p+1` is accepted iff the
/// combined POD still satisfies every per-POD cap (statement table,
/// merkle pools, CPV cap, signed_by / public_key_of, input-pod cap,
/// publish cap). Each successful merge drops K by 1.
///
/// Motivated by the `cracked_refinery_milp_multi_seed_pair_stability`
/// probe: 58% of the heuristic's violations of MILP-stable pairs are
/// adjacent-POD splits. Merging adjacent PODs is the cheapest fix for
/// that class, and it directly reduces K rather than just balancing.
/// Long-range cluster splits (the other 42%) aren't repaired here;
/// those need cluster-aware admission, not local repair.
fn refine_via_merges(input: &InputShape, mut output: OutputShape) -> OutputShape {
    loop {
        let mut applied = false;
        for p in 0..output.pod_count.saturating_sub(1) {
            if let Some(merged) = try_merge_adjacent(input, &output, p) {
                output = merged;
                applied = true;
                break;
            }
        }
        if !applied {
            break;
        }
    }
    output
}

/// Try to merge POD `p` and POD `p+1`. Returns `Some(new_output)` if
/// the combined POD passes [`segment_feasible_with`] against a
/// freshly-reconstructed topo ordering, `None` otherwise.
fn try_merge_adjacent(
    input: &InputShape,
    output: &OutputShape,
    p: usize,
) -> Option<OutputShape> {
    let pod_count = output.pod_count;
    if p + 1 >= pod_count {
        return None;
    }
    let new_pod_count = pod_count - 1;

    let mut merged_stmts: Vec<usize> = output.pod_statements[p].clone();
    merged_stmts.extend_from_slice(&output.pod_statements[p + 1]);
    merged_stmts.sort();

    let mut new_pod_statements: Vec<Vec<usize>> = Vec::with_capacity(new_pod_count);
    for (q, stmts) in output.pod_statements.iter().enumerate() {
        if q == p {
            new_pod_statements.push(merged_stmts.clone());
        } else if q == p + 1 {
            continue;
        } else {
            new_pod_statements.push(stmts.clone());
        }
    }

    // Reconstruct a global topo ordering as the concatenation of each
    // POD's stmts in chain order, topo-sorted within the POD. Within-
    // POD order doesn't matter for `pod_statements` (it's stored
    // sorted by stmt index) but `segment_feasible_with` needs an
    // actual topo sequence so `max_consumer_pos` is meaningful.
    let consumers = input.consumers();
    let mut ordering: Vec<usize> = Vec::with_capacity(input.num_statements());
    for stmts in &new_pod_statements {
        ordering.extend(topo_sort_subset(input, stmts, &consumers));
    }
    if ordering.len() != input.num_statements() {
        return None;
    }

    let pos_in_ordering = build_pos_in_ordering(&ordering);
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    let mut workspace = DpWorkspace::default();

    let mut pos = 0_usize;
    for (idx, stmts) in new_pod_statements.iter().enumerate() {
        let a = pos;
        let b = pos + stmts.len();
        let is_terminal = idx + 1 == new_pod_count;
        if !segment_feasible_with(
            &ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            a,
            b,
            is_terminal,
            &mut workspace,
        ) {
            return None;
        }
        pos = b;
    }

    let mut new_republished: Vec<BTreeSet<usize>> = Vec::with_capacity(new_pod_count);
    for (q, rep) in output.pod_republished_externals.iter().enumerate() {
        if q == p {
            let mut combined = rep.clone();
            combined.extend(output.pod_republished_externals[p + 1].iter().copied());
            new_republished.push(combined);
        } else if q == p + 1 {
            continue;
        } else {
            new_republished.push(rep.clone());
        }
    }

    Some(OutputShape {
        pod_count: new_pod_count,
        pod_statements: new_pod_statements,
        pod_republished_externals: new_republished,
    })
}

/// Topological sort restricted to a subset of statement indices.
/// Returns the subset in some valid order; returns a shorter list iff
/// the subset has a cycle (which shouldn't happen for a well-formed
/// partition since the global DAG is acyclic).
fn topo_sort_subset(
    input: &InputShape,
    stmts: &[usize],
    consumers: &[Vec<usize>],
) -> Vec<usize> {
    let in_subset: HashSet<usize> = stmts.iter().copied().collect();
    let n = input.num_statements();
    let mut indegree = vec![0_usize; n];
    for &s in stmts {
        for dep in &input.dep_edges[s] {
            if let AbstractDep::Internal(d) = dep {
                if in_subset.contains(d) {
                    indegree[s] += 1;
                }
            }
        }
    }
    let mut ready: Vec<usize> = stmts
        .iter()
        .copied()
        .filter(|s| indegree[*s] == 0)
        .collect();
    let mut result = Vec::with_capacity(stmts.len());
    while let Some(s) = ready.pop() {
        result.push(s);
        for &c in &consumers[s] {
            if in_subset.contains(&c) {
                indegree[c] -= 1;
                if indegree[c] == 0 {
                    ready.push(c);
                }
            }
        }
    }
    result
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

/// Bin-packing Kahn topological sort. At each step, prefers ready
/// statements that fit into the segment currently being built without
/// exceeding any per-POD cap; when nothing fits, closes the segment and
/// opens a new one at the next ready statement.
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
    // Per-statement distinct-consumer count. `consumers[d]` may name
    // the same statement twice when one consumer has two `Internal(d)`
    // entries; we want the distinct count for the publish-cap export
    // book-keeping so `unfinished_consumers[d]` matches the number of
    // `commit_extend` calls that will decrement it.
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
    let mut state = GreedyState::default();
    state.unfinished_consumers = vec![0; n];
    let mut ready: Vec<usize> = (0..n).filter(|&s| indegree[s] == 0).collect();

    // Coupling-aware tiebreak helper: count Internal deps of `s` that
    // are already in the current segment. Encourages tight clusters
    // (CPV body+head slices, dep-chained statements) to admit
    // contiguously rather than letting unrelated ready statements
    // wedge between them. Motivated by the
    // `cracked_refinery_milp_seed_stability` probe: dep-tight clusters
    // consistently co-locate across MILP seeds, so surfacing them
    // during admission matches MILP's local structure.
    fn coupling_score(
        deps: &[AbstractDep],
        pos_built: &[usize],
        segment_start: usize,
    ) -> usize {
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
        // Pick the next statement, and decide whether to extend the
        // running segment or open a new one. With an empty segment any
        // ready statement fits, so we skip the per-statement `can_extend`
        // probe and just pick lowest tiebreak. With a non-empty segment
        // we prefer the lowest-tiebreak ready statement that fits within
        // the per-POD caps, falling back to the lowest-tiebreak overall
        // when nothing fits (in which case we close the segment).
        let (chosen_idx, opens_new_segment) = if state.totals.num_statements == 0 {
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
/// `params.max_open_input_statements`; the chain slot counts as one
/// input-pod iff there are any prev-pod producers.
fn tree_imports_ok(
    n_producers: usize,
    n_ext_imports: usize,
    n_ext_pods: usize,
    params: &Params,
) -> bool {
    n_producers + n_ext_imports <= params.max_open_input_statements
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
    /// Tight count of statements admitted to the current segment that
    /// would land on the chain tree if the segment closed now: a
    /// statement is exported iff it still has at least one consumer
    /// outside the segment OR it's in `output_public_indices`. As
    /// admissions co-locate consumers with their producers, the count
    /// can DECREASE. `unfinished_consumers[s]` tracks the remaining
    /// out-of-segment consumer count per segment member; when it hits
    /// zero (and `s` isn't an output-public), `s` drops out of the
    /// exported set.
    exported_count: usize,
    /// For each statement that has been admitted at any point, the
    /// number of distinct internal consumers not yet admitted to the
    /// CURRENT segment. Sized once at the top of `kahn_bin_packing`.
    /// `usize::MAX` for statements not yet admitted to any segment.
    /// On segment reset, entries for the previous segment's members
    /// are stale but irrelevant — the export check only looks at
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
        // Don't touch `unfinished_consumers`: its entries are
        // tagged-by-position via `pos_built` and the segment range
        // `[a..)`. Old entries fall out of scope once `self.a`
        // advances past them.
    }

    /// Would the current segment still satisfy all per-POD caps after
    /// adding `cost` / `deps`? On success, returns the number of *new*
    /// import slots (chain + external) the admission would consume — used
    /// by the bin-packing tiebreak to prefer admissions that don't drag
    /// fresh imports into the segment. `None` means infeasible. Mutates
    /// only the `scratch_*` fields.
    fn can_extend(
        &mut self,
        cost: &StatementCost,
        deps: &[AbstractDep],
        pos_of: &[usize],
        is_exporter: bool,
        output_pub_set: &HashSet<usize>,
        params: &Params,
    ) -> Option<usize> {
        // Tight publish-cap probe. Each of the candidate's in-segment
        // Internal deps `d` loses one unfinished consumer; if d's
        // count would drop to zero and d isn't an output-public, d
        // exits the exported set so the segment can absorb one extra
        // would-be-export.
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
        if tentative.num_statements + n_producers + n_ext_imports > params.max_statements {
            return None;
        }
        Some(self.scratch_new_producers.len() + self.scratch_new_ext_imports.len())
    }

    /// Apply the extension to the segment. Caller must have verified
    /// feasibility via [`can_extend`]; the mutation here is unchecked.
    fn commit_extend(
        &mut self,
        s: usize,
        cost: &StatementCost,
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
        // Decrement unfinished-consumer counts for each in-segment dep
        // of `s`; if d's count reaches zero (and d isn't an
        // output-public) d exits the exported set.
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
        // Seed s's unfinished-consumer count with its total distinct
        // internal consumers; s joins the exported set if any consumer
        // exists or s is an output-public.
        self.unfinished_consumers[s] = distinct_consumer_count;
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

/// Reusable scratch for [`run_dp`]'s segment-feasibility checks. The
/// inner loop fires up to `n * W` feasibility checks per ordering
/// (where W = max_priv_statements), so reusing these buffers across
/// calls keeps allocation off the hot path. Each set is `.clear()`ed
/// at the top of every check, which is O(active) (active size is
/// bounded by `MAX_TREE_IMPORTS`).
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

/// Generate a per-statement priority vector by ranking a random
/// permutation. The resulting `prio_of[s]` is `s`'s rank in the shuffle.
fn random_priority(rng: &mut ChaCha20Rng, n: usize) -> Vec<usize> {
    let mut shuffled: Vec<usize> = (0..n).collect();
    shuffled.shuffle(rng);
    let mut prio_of = vec![0_usize; n];
    for (rank, &s) in shuffled.iter().enumerate() {
        prio_of[s] = rank;
    }
    prio_of
}

/// Generate the candidate orderings the cutter will try. Bin-packing
/// goes first (strongest single seed on production-cap workloads),
/// then DFS-from-sinks (a subtree-contiguous topological ordering
/// targeted at workloads with wide producer-consumer index gaps),
/// then the random-priority orderings for variety.
///
/// Duplicates would just mean cutting the same sequence twice; with one
/// deterministic + ten random seeds, collisions are vanishingly rare
/// and the redundant cut is cheaper than scanning for duplicates.
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

/// Per-statement position lookup against an ordering. `pos_in_ordering[s]`
/// returns the position of statement `s` in the ordering. Built once
/// and shared across the many `segment_feasible_with` calls the inner
/// loop fires; rebuilding it per call would dominate that loop.
fn build_pos_in_ordering(ordering: &[usize]) -> Vec<usize> {
    let n = ordering.len();
    let mut pos = vec![usize::MAX; n];
    for (i, &s) in ordering.iter().enumerate() {
        pos[s] = i;
    }
    pos
}

/// Build a topological ordering via depth-first search from sinks
/// (statements with no internal consumers), recursing into deps before
/// emitting each statement. The result is a forward topological order
/// (producers before consumers) with the property that each
/// statement's entire dep-closure is emitted contiguously immediately
/// before it. For workloads with definition-then-distant-use patterns
/// (e.g. cracked-refinery's `IsX` type assertions used much later in
/// the replay chain), this shortens producer-consumer index gaps
/// versus the canonical user-input order, giving bin-packing a
/// chance to admit each definition-and-use cluster as one segment.
pub(super) fn build_dfs_topo_order(input: &InputShape) -> Vec<usize> {
    let n = input.num_statements();
    let consumers = input.consumers();
    let mut visited = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    for s in 0..n {
        if consumers[s].is_empty() && !visited[s] {
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
    let deps = &input.dep_edges[s];
    for idx in 0..deps.len() {
        if let AbstractDep::Internal(d) = deps[idx] {
            dfs_emit(d, input, visited, order);
        }
    }
    order.push(s);
}

/// Per-statement max-consumer-position lookup against an ordering.
/// `max_consumer_pos[s]` is the largest position in `ordering` of any
/// statement that has `s` as an `Internal` dep, or 0 if `s` has no
/// internal consumers. Drives the per-segment publish-cap check: `s` is
/// exported from segment `[a..p]` iff `max_consumer_pos[s] >= p` (some
/// consumer lives after the segment) or `s` is in
/// `output_public_indices` (the output POD pulls it via chain).
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

/// Simulate the greedy partition over a fixed ordering: extend each
/// segment as long as feasibility holds, close at the first cap-bust.
/// Mirrors what bin-packing's `can_extend` does on its own emitted
/// ordering. Used by diagnostic probes to compare `K_bp_greedy`
/// against the DP's `K_bp_dp` on the same ordering.
///
/// Returns `None` if any single statement is infeasible as a 1-stmt
/// segment (e.g. its costs already exceed a per-POD cap); otherwise
/// the number of segments greedy produces. Does not apply terminal
/// (output-public) feasibility — the comparison value is greedy-K,
/// not DP-K-terminal.
pub(super) fn simulate_greedy_k(input: &InputShape, ordering: &[usize]) -> Option<usize> {
    let n = ordering.len();
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    let mut ws = DpWorkspace::default();
    let mut k = 0_usize;
    let mut a = 0_usize;
    while a < n {
        if !segment_feasible_with(
            ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            a,
            a + 1,
            false,
            &mut ws,
        ) {
            return None;
        }
        let mut p = a + 1;
        while p < n
            && segment_feasible_with(
                ordering,
                &pos_in_ordering,
                &max_consumer_pos,
                &output_pub_set,
                input,
                a,
                p + 1,
                false,
                &mut ws,
            )
        {
            p += 1;
        }
        k += 1;
        a = p;
    }
    Some(k)
}

/// Greedy partition of `ordering` into segments, enforcing terminal
/// (output-public) feasibility on the final segment. Mirrors what
/// `simulate_greedy_k` does for non-terminal segments, then verifies
/// the last one as terminal. Returns the segment boundary list or
/// `None` if no valid partition exists for this ordering (a single
/// statement cap-busts, or the trailing segment fails terminal
/// availability and greedy can't backtrack to fix it).
///
/// This is the no-DP counterpart to `run_dp`, for the DP-vs-greedy
/// sweep that probes whether the DP layer is load-bearing.
fn greedy_segments_with_terminal(
    ordering: &[usize],
    input: &InputShape,
) -> Option<Vec<(usize, usize)>> {
    let n = ordering.len();
    if n == 0 {
        return Some(Vec::new());
    }
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    let mut ws = DpWorkspace::default();
    let mut segments: Vec<(usize, usize)> = Vec::new();
    let mut a = 0_usize;
    while a < n {
        if !segment_feasible_with(
            ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            a,
            a + 1,
            false,
            &mut ws,
        ) {
            return None;
        }
        let mut p = a + 1;
        while p < n
            && segment_feasible_with(
                ordering,
                &pos_in_ordering,
                &max_consumer_pos,
                &output_pub_set,
                input,
                a,
                p + 1,
                false,
                &mut ws,
            )
        {
            p += 1;
        }
        segments.push((a, p));
        a = p;
    }
    let (last_a, last_p) = *segments
        .last()
        .expect("non-empty ordering produced no segments");
    if !segment_feasible_with(
        ordering,
        &pos_in_ordering,
        &max_consumer_pos,
        &output_pub_set,
        input,
        last_a,
        last_p,
        true,
        &mut ws,
    ) {
        return None;
    }
    Some(segments)
}

/// No-DP variant of [`partition`]: tries every candidate ordering and
/// keeps the lowest-K result, but uses greedy left-to-right cuts
/// ([`greedy_segments_with_terminal`]) instead of the DP. Used by the
/// DP-vs-greedy sweep to measure whether the DP layer contributes any
/// K-improvement beyond what greedy achieves on the same orderings.
pub(super) fn partition_greedy_only(input: &InputShape) -> Option<OutputShape> {
    let n = input.num_statements();
    if n == 0 {
        return Some(OutputShape {
            pod_count: 0,
            pod_statements: vec![],
            pod_republished_externals: vec![],
        });
    }

    let lower_bound = resource_lower_bound_k(input);
    let mut best: Option<OutputShape> = None;

    for ordering in candidate_orderings(input) {
        let Some(segments) = greedy_segments_with_terminal(&ordering, input) else {
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

/// Workspace-backed feasibility check. Returns true iff segment `[a..p]`
/// fits in one POD; `is_terminal` additionally enforces output-POD
/// availability for output-public statements upstream of `a`.
///
/// Reuses `workspace` for the membership sets and the distinct-CP dedup
/// buffer; both are reset per call but their underlying allocations are
/// shared across the ~28K calls in one `run_dp`.
fn segment_feasible_with(
    ordering: &[usize],
    pos_in_ordering: &[usize],
    max_consumer_pos: &[usize],
    output_pub_set: &HashSet<usize>,
    input: &InputShape,
    a: usize,
    p: usize,
    is_terminal: bool,
    workspace: &mut DpWorkspace,
) -> bool {
    let params = &input.params;
    let segment = &ordering[a..p];
    if segment.is_empty() || segment.len() > params.max_statements {
        return false;
    }

    // Single pass: per-statement, accumulate scalar sums + distinct CPs
    // (cap-checked via [`ResourceTotals::fits_in_pod`]) and record
    // input-tree imports. Input-tree imports come in two flavours, both
    // capped together by `MAX_TREE_IMPORTS` because the POD circuit reads
    // them through the same input-tree slots:
    // - prev-pod producers: statements produced in `[0..a)` (slot 0,
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
                    if pos_in_ordering[*d] < a {
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
        // busted there's no recovery. Cheap check (StampSet len is O(1))
        // and saves the remaining statements' worth of inserts on
        // infeasible segments.
        if workspace.prev_pod_producers.len() + workspace.external_imports.len()
            > params.max_open_input_statements
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
        // at or beyond `p`, or that is an output-public (the terminal POD
        // pulls it from the chain), occupies one slot on the chain tree
        // this POD appends to. The terminal POD doesn't extend the chain
        // — its fresh-tree size is `|output_public_indices|`, pre-checked
        // by callers before invoking the partitioner.
        let mut exports = 0_usize;
        for &s in segment {
            if max_consumer_pos[s] >= p || output_pub_set.contains(&s) {
                exports += 1;
            }
        }
        return exports <= params.max_public_statements;
    }

    // Terminal: output_public statements in the prefix become additional
    // prev-pod producers (the output POD must republish them on its
    // fresh tree).
    for &out_pub in &input.output_public_indices {
        if pos_in_ordering[out_pub] < a {
            workspace.prev_pod_producers.insert(out_pub);
        }
    }
    let n_chain_imports_terminal = workspace.prev_pod_producers.len();
    if segment.len() + n_chain_imports_terminal + n_ext_imports > params.max_statements {
        return false;
    }
    tree_imports_ok(n_chain_imports_terminal, n_ext_imports, n_ext_pods, params)
}

/// Cut `ordering` into the fewest feasible PODs under per-POD caps.
/// Returns the boundary list `[(a0, b0), (a1, b1), ..., (ak, n)]` (one
/// tuple per POD, in chain order), or `None` if no valid partition
/// exists for this ordering.
///
/// Dynamic programming over prefixes. `dp[p]` is the min-K non-terminal partition of
/// `[0..p]`, computed by trying every segment `[a..p]` with `a` in
/// `[p-W..p)` against [`segment_feasible_with`]. The output (terminal)
/// segment falls out of a single scan over `[a..n]` for `a` in
/// `[n-W..n)` after the main loop; pulling it out keeps the `dp[]`
/// array single-flavoured and touches at most `W` extra segments,
/// negligible next to the main loop's `n * W` work.
fn run_dp(ordering: &[usize], input: &InputShape) -> Option<Vec<(usize, usize)>> {
    let n = ordering.len();
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let consumers = input.consumers();
    let max_consumer_pos = build_max_consumer_pos(&consumers, &pos_in_ordering);
    let output_pub_set: HashSet<usize> = input.output_public_indices.iter().copied().collect();
    // Any segment with more than `max_priv_statements` slots is
    // infeasible, so we only need to consider cuts within the last W
    // positions. That caps the inner loop at W choices per `p`, giving
    // the O(n * W^2) total the module doc claims.
    let max_segment_len = input.params.max_statements;

    // dp[p] = Some((min_k, prev_a)) iff `[0..p]` partitions into `min_k`
    // non-terminal segments, with the last segment being `[prev_a..p]`.
    let mut dp: Vec<Option<(usize, usize)>> = vec![None; n + 1];
    let mut workspace = DpWorkspace::default();

    dp[0] = Some((0, 0));

    for p in 1..=n {
        let a_lo = p.saturating_sub(max_segment_len);
        let mut best: Option<(usize, usize)> = None;
        for (a, slot) in dp.iter().take(p).enumerate().skip(a_lo) {
            let Some((prev_k, _)) = *slot else { continue };
            if segment_feasible_with(
                ordering,
                &pos_in_ordering,
                &max_consumer_pos,
                &output_pub_set,
                input,
                a,
                p,
                false,
                &mut workspace,
            ) {
                let k = prev_k + 1;
                if best.is_none_or(|(cur_k, _)| k < cur_k) {
                    best = Some((k, a));
                }
            }
        }
        dp[p] = best;
    }

    // Terminal scan: pick the best `a` such that `[a..n]` is a valid
    // output segment and `dp[a]` is reachable.
    let a_lo = n.saturating_sub(max_segment_len);
    let mut end_start: Option<usize> = None;
    let mut best_k = usize::MAX;
    for (a, dp_entry) in dp.iter().enumerate().take(n).skip(a_lo) {
        let Some((prev_k, _)) = *dp_entry else {
            continue;
        };
        if segment_feasible_with(
            ordering,
            &pos_in_ordering,
            &max_consumer_pos,
            &output_pub_set,
            input,
            a,
            n,
            true,
            &mut workspace,
        ) && prev_k + 1 < best_k
        {
            best_k = prev_k + 1;
            end_start = Some(a);
        }
    }
    let mut end_start = end_start?;

    let mut segments_rev = vec![(end_start, n)];
    while end_start > 0 {
        let (_, prev_a) = dp[end_start].expect("dp reachability already established");
        segments_rev.push((prev_a, end_start));
        end_start = prev_a;
    }
    segments_rev.reverse();
    Some(segments_rev)
}

/// Cut a single externally-supplied topological ordering into PODs.
/// Returns `None` only when a per-statement cap is itself violated: the
/// cutter is optimal over its given ordering, so any other failure mode
/// would mean that ordering simply has no valid partition. Used by
/// tests that want to compare the partitioner's output against an
/// oracle-derived ordering.
pub(super) fn partition_with_ordering(
    input: &InputShape,
    ordering: &[usize],
) -> Option<OutputShape> {
    let segments = run_dp(ordering, input)?;
    Some(reconstruct(ordering, &segments))
}

fn reconstruct(ordering: &[usize], segments: &[(usize, usize)]) -> OutputShape {
    let pod_count = segments.len();
    let pod_statements: Vec<Vec<usize>> = segments
        .iter()
        .map(|&(a, p)| {
            let mut stmts: Vec<usize> = ordering[a..p].to_vec();
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
        use super::super::cost::StatementCost;
        InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
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
        // Default Params: max_priv_statements is large, single POD should
        // accommodate a handful of independent statements.
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
        use super::super::cost::StatementCost;
        let params = Params::default();
        let n = params.max_open_input_statements + 1;
        let input = InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
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
        use super::super::cost::StatementCost;
        let params = Params {
            max_statements: 3,
            ..Params::default()
        };
        let input = InputShape {
            costs: (0..4).map(|_| StatementCost::default()).collect(),
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

    /// DP vs greedy random sweep. For each generated input, compares
    /// `partition` (full pipeline, DP cuts per ordering) against
    /// `partition_greedy_only` (same orderings, greedy cuts). Reports the
    /// K-diff distribution and the count of "DP rescue" cases where
    /// greedy is infeasible but DP isn't (the empirical justification
    /// for the DP layer). Asserts on the inverse direction (greedy
    /// feasible, DP infeasible) which should never happen.
    ///
    /// Shares its RNG seed and parameter variants with the DP-vs-MILP
    /// parity sweep so the two sweeps probe the same distribution.
    #[test]
    fn dp_vs_greedy_random_sweep() {
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
                    max_signed_by: 2,
                    ..Params::default()
                },
            ),
        ];
        let n_values: Vec<usize> = vec![8, 12, 16, 24, 32];
        let trials_per_combo: usize = 25;

        let mut rng = ChaCha20Rng::seed_from_u64(0xDEADBEEF);
        let mut checked = 0_usize;
        let mut both_feasible = 0_usize;
        let mut dp_rescue = 0_usize;
        let mut k_diff: BTreeMap<i64, usize> = BTreeMap::new();
        let mut k_diff_by_variant: BTreeMap<&str, BTreeMap<i64, usize>> = BTreeMap::new();

        for (label, params) in &param_variants {
            for &n in &n_values {
                for trial in 0..trials_per_combo {
                    let input = random_input(&mut rng, n, params.clone());
                    let dp_out = partition(&input);
                    let greedy_out = partition_greedy_only(&input);

                    checked += 1;
                    match (&dp_out, &greedy_out) {
                        (Some(d), Some(g)) => {
                            both_feasible += 1;
                            let diff = g.pod_count as i64 - d.pod_count as i64;
                            *k_diff.entry(diff).or_insert(0) += 1;
                            *k_diff_by_variant
                                .entry(label)
                                .or_default()
                                .entry(diff)
                                .or_insert(0) += 1;
                            if diff < 0 {
                                panic!(
                                    "greedy returned smaller K than DP on [{} n={} trial={}]: \
                                     DP={}, greedy={}",
                                    label, n, trial, d.pod_count, g.pod_count
                                );
                            }
                        }
                        (Some(d), None) => {
                            dp_rescue += 1;
                            eprintln!(
                                "DP RESCUE [{} n={} trial={}]: DP={} PODs, greedy=none",
                                label, n, trial, d.pod_count
                            );
                        }
                        (None, Some(_)) => {
                            panic!(
                                "greedy feasible but DP infeasible on [{} n={} trial={}] \
                                 (DP considers greedy's cuts as a subset of its choices, \
                                 so this should never happen)",
                                label, n, trial
                            );
                        }
                        (None, None) => {}
                    }
                }
            }
        }

        eprintln!();
        eprintln!("=== DP-vs-greedy random sweep ===");
        eprintln!(
            "  checked={} both_feasible={} dp_rescue={}",
            checked, both_feasible, dp_rescue
        );
        eprintln!("  K diff (K_greedy - K_dp) overall:");
        for (diff, count) in &k_diff {
            eprintln!("    diff={:+}: {}", diff, count);
        }
        eprintln!("  K diff by variant:");
        for (variant, dist) in &k_diff_by_variant {
            eprint!("    {}: ", variant);
            for (diff, count) in dist {
                eprint!("({:+}: {}) ", diff, count);
            }
            eprintln!();
        }

        // The right-direction divergence ("greedy feasible, DP infeasible")
        // would be a bug and is panicked above. The other direction ("DP
        // feasible, greedy infeasible") is reported as `dp_rescue` and is
        // the empirical justification for the DP layer; no assertion on it
        // because the goal here is to *measure* DP's contribution, not
        // enforce it.
    }
}
