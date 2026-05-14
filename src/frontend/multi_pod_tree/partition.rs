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
//!   walk produces an infeasible partition, which can happen if a POD
//!   requires more than the available input statements. See
//!   [`dp_recovers_on_fan_in`] for an example.

use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap, HashSet},
};

use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaCha20Rng;

use super::{
    cost::{CustomPredicateId, ResourceTotals, StatementCost, MAX_TREE_IMPORTS},
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

    let mut ordering: Vec<usize> = Vec::with_capacity(n);
    let mut pos_built = vec![usize::MAX; n];
    let mut state = GreedyState::default();
    let mut ready: Vec<usize> = (0..n).filter(|&s| indegree[s] == 0).collect();

    while !ready.is_empty() {
        // Pick the next statement, and decide whether to extend the
        // running segment or open a new one. With an empty segment any
        // ready statement fits, so we skip the per-statement `can_extend`
        // probe and just pick lowest tiebreak. With a non-empty segment
        // we prefer the lowest-tiebreak ready statement that fits within
        // the per-POD caps, falling back to the lowest-tiebreak overall
        // when nothing fits (in which case we close the segment).
        let (chosen_idx, opens_new_segment) = if state.totals.num_statements == 0 {
            let i = ready
                .iter()
                .enumerate()
                .min_by_key(|(_, &s)| tiebreak_priority[s])
                .expect("ready is non-empty")
                .0;
            (i, true)
        } else {
            let mut best_fit: Option<usize> = None;
            let mut best_fit_prio = usize::MAX;
            let mut best_overall = 0_usize;
            let mut best_overall_prio = usize::MAX;
            for (i, &s) in ready.iter().enumerate() {
                let prio = tiebreak_priority[s];
                if prio < best_overall_prio {
                    best_overall_prio = prio;
                    best_overall = i;
                }
                let cost = &input.costs[s];
                let deps = &input.dep_edges[s];
                if state.can_extend(cost, deps, &pos_built, params) && prio < best_fit_prio {
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
        state.commit_extend(cost, deps, &pos_built);
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
/// slots) and input-pods. Tree imports are capped by `MAX_TREE_IMPORTS`;
/// the chain slot counts as one input-pod iff there are any prev-pod
/// producers.
fn tree_imports_ok(
    n_producers: usize,
    n_ext_imports: usize,
    n_ext_pods: usize,
    max_input_pods: usize,
) -> bool {
    n_producers + n_ext_imports <= MAX_TREE_IMPORTS
        && usize::from(n_producers > 0) + n_ext_pods <= max_input_pods
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
    /// Scratch buffers used inside [`can_extend`] for deduplication.
    /// Cleared on each call to avoid churning allocations.
    scratch_new_producers: Vec<usize>,
    scratch_new_ext_imports: Vec<usize>,
    scratch_new_ext_pods: Vec<usize>,
}

impl GreedyState {
    fn reset(&mut self) {
        self.a = 0;
        self.totals = ResourceTotals::default();
        self.distinct_cps.clear();
        self.prev_pod_producers.clear();
        self.external_imports.clear();
        self.external_pods.clear();
    }

    /// Would the current segment still satisfy all per-POD caps after
    /// adding `cost` / `deps`? Callers that want to peek before
    /// committing (like the bin-packing ordering generator) use this
    /// directly. Mutates only the `scratch_*` fields.
    fn can_extend(
        &mut self,
        cost: &StatementCost,
        deps: &[AbstractDep],
        pos_of: &[usize],
        params: &Params,
    ) -> bool {
        let new_cp_count = cost
            .custom_predicates_ids
            .iter()
            .filter(|id| !self.distinct_cps.contains(id))
            .count();
        let mut tentative = self.totals.clone();
        tentative.add(cost);
        tentative.distinct_custom_predicates = self.distinct_cps.len() + new_cp_count;
        if !tentative.fits_in_pod(params) {
            return false;
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
                AbstractDep::External { pod, premise } => {
                    if !self.external_imports.contains(premise)
                        && !self.scratch_new_ext_imports.contains(premise)
                    {
                        self.scratch_new_ext_imports.push(*premise);
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
        tree_imports_ok(
            n_producers,
            n_ext_imports,
            n_ext_pods,
            params.max_input_pods,
        )
    }

    /// Apply the extension to the segment. Caller must have verified
    /// feasibility via [`can_extend`]; the mutation here is unchecked.
    fn commit_extend(&mut self, cost: &StatementCost, deps: &[AbstractDep], pos_of: &[usize]) {
        self.totals.add(cost);
        for id in &cost.custom_predicates_ids {
            if !self.distinct_cps.contains(id) {
                self.distinct_cps.push(id.clone());
            }
        }
        self.totals.distinct_custom_predicates = self.distinct_cps.len();
        for dep in deps {
            match dep {
                AbstractDep::Internal(d) => {
                    if pos_of[*d] < self.a && !self.prev_pod_producers.contains(d) {
                        self.prev_pod_producers.push(*d);
                    }
                }
                AbstractDep::External { pod, premise } => {
                    if !self.external_imports.contains(premise) {
                        self.external_imports.push(*premise);
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
    /// External premises imported by the current segment.
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

/// Non-terminal-only per-segment feasibility check, self-contained
/// (builds its own `pos_in_ordering` and `DpWorkspace`). Callers in a
/// hot loop should use `segment_feasible_with` to reuse allocations.
pub(super) fn segment_feasible(ordering: &[usize], input: &InputShape, a: usize, p: usize) -> bool {
    let pos_in_ordering = build_pos_in_ordering(ordering);
    let mut ws = DpWorkspace::default();
    segment_feasible_with(ordering, &pos_in_ordering, input, a, p, false, &mut ws)
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
    input: &InputShape,
    a: usize,
    p: usize,
    is_terminal: bool,
    workspace: &mut DpWorkspace,
) -> bool {
    let params = &input.params;
    let segment = &ordering[a..p];
    if segment.is_empty() || segment.len() > params.max_priv_statements() {
        return false;
    }

    // Single pass: per-statement, accumulate scalar sums + distinct CPs
    // (cap-checked via [`ResourceTotals::fits_in_pod`]) and record
    // input-tree imports. Input-tree imports come in two flavours, both
    // capped together by `MAX_TREE_IMPORTS` because the POD circuit reads
    // them through the same input-tree slots:
    // - prev-pod producers: statements produced in `[0..a)` (slot 0,
    //   the chain slot connecting this POD to its predecessor).
    // - external imports: external premises (slots 1..N).
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
                AbstractDep::External { pod, premise } => {
                    workspace.external_imports.insert(*premise);
                    workspace.external_pods.insert(*pod);
                }
            }
        }
        // Mid-loop bail: the chain-slot + external-slot tree-imports
        // cap can only grow as we add more statements, so once it's
        // busted there's no recovery. Cheap check (StampSet len is O(1))
        // and saves the remaining statements' worth of inserts on
        // infeasible segments.
        if workspace.prev_pod_producers.len() + workspace.external_imports.len() > MAX_TREE_IMPORTS
        {
            return false;
        }
    }

    let n_ext_imports = workspace.external_imports.len();
    let n_ext_pods = workspace.external_pods.len();
    let non_terminal = tree_imports_ok(
        workspace.prev_pod_producers.len(),
        n_ext_imports,
        n_ext_pods,
        params.max_input_pods,
    );
    if !non_terminal || !is_terminal {
        return non_terminal;
    }

    // Terminal: output_public statements in the prefix become additional
    // prev-pod producers (the output POD must republish them on its
    // fresh tree).
    for &out_pub in &input.output_public_indices {
        if pos_in_ordering[out_pub] < a {
            workspace.prev_pod_producers.insert(out_pub);
        }
    }
    tree_imports_ok(
        workspace.prev_pod_producers.len(),
        n_ext_imports,
        n_ext_pods,
        params.max_input_pods,
    )
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
    // Any segment with more than `max_priv_statements` slots is
    // infeasible, so we only need to consider cuts within the last W
    // positions. That caps the inner loop at W choices per `p`, giving
    // the O(n * W^2) total the module doc claims.
    let max_segment_len = input.params.max_priv_statements();

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
            premise_pod: vec![],
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
            premise_pod: vec![],
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
        // Force a 2-POD split via tight max_priv_statements.
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            ..Params::default()
        };
        // max_priv_statements = 2; 3 statements need 2 PODs.
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
    fn external_imports_count_against_max_tree_imports() {
        // n statements, each with one External dep to a distinct premise
        // from a single external POD. With one external pod, `max_input_pods`
        // can't force a split, so the only constraint that drives K > 1 is
        // the combined import cap.
        use super::super::cost::StatementCost;
        let n = MAX_TREE_IMPORTS + 1;
        let input = InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
            dep_edges: (0..n)
                .map(|i| vec![AbstractDep::External { pod: 0, premise: i }])
                .collect(),
            output_public_indices: vec![0],
            num_external_pods: 1,
            premise_pod: vec![0; n],
            params: Params::default(),
        };
        let out = partition(&input).expect("should partition");
        assert!(
            out.pod_count >= 2,
            "external imports must count against MAX_TREE_IMPORTS, but {} \
             external imports packed into a single POD",
            n
        );
    }

    #[test]
    fn dependency_chain_respects_topo_order() {
        // 4 statements where each depends on the previous. With
        // max_priv_statements = 2, this should split into 2 PODs with
        // statements [0,1] and [2,3].
        use super::super::cost::StatementCost;
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
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
            premise_pod: vec![],
            params,
        };
        let out = partition(&input).expect("should partition");
        assert_eq!(out.pod_count, 2);
        // Topo order requires 0 before 1, 1 before 2, 2 before 3. With
        // segments of size 2, the only valid partition is {0,1} then {2,3}.
        assert_eq!(out.pod_statements[0], vec![0, 1]);
        assert_eq!(out.pod_statements[1], vec![2, 3]);
    }

    /// Fan-in DAG: 21 zero-cost producers and a single consumer T with
    /// `Internal` deps on every producer. `MAX_TREE_IMPORTS = 20`, so any
    /// segment containing T can pull at most 20 prev-pod producers
    /// through its chain slot, so T's segment must hold at least one
    /// producer locally.
    ///
    /// Same-ordering greedy packing fails on this DAG: it fills segment
    /// 1 to cap (21 statements at `max_priv = 21`), leaving T alone in
    /// a fresh segment needing 21 prev-pod producers via the chain
    /// slot, which busts `MAX_TREE_IMPORTS`. Cutting earlier rescues
    /// it: segment 1 holds just [stmt 0], segment 2 holds [1..21] = 20
    /// producers and T at cap, and T's chain slot only has to pull one
    /// prev-pod producer.
    ///
    /// This is why the cutting pass isn't just an optimisation; it's
    /// soundness insurance for fan-in-bound workloads. A naive
    /// left-to-right greedy walk on the same ordering would give up.
    #[test]
    fn dp_recovers_on_fan_in() {
        use super::super::cost::StatementCost;

        let n_producers = 21usize;
        let n = n_producers + 1;
        let consumer = n_producers;
        let params = Params {
            max_statements: 23,
            max_public_statements: 2,
            ..Params::default()
        };
        assert_eq!(
            params.max_priv_statements(),
            21,
            "test relies on max_priv = 21 = n_producers so segment 1 fills exactly at cap"
        );

        let mut dep_edges: Vec<Vec<AbstractDep>> = (0..n).map(|_| Vec::new()).collect();
        dep_edges[consumer] = (0..n_producers).map(AbstractDep::Internal).collect();
        let input = InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
            dep_edges,
            output_public_indices: vec![consumer],
            num_external_pods: 0,
            premise_pod: vec![],
            params,
        };

        let identity: Vec<usize> = (0..n).collect();
        let ordering = kahn_with_priority(&input, &identity).expect("DAG must be acyclic");
        assert_eq!(
            ordering, identity,
            "source-order Kahn on a single-sink fan-in DAG yields 0..n"
        );

        let dp_out = partition_with_ordering(&input, &ordering)
            .expect("DP must find a feasible partition on the source-order ordering");
        assert_eq!(
            dp_out.pod_count, 2,
            "DP cuts at (0..1, 1..22) so T's segment imports only one producer via chain"
        );
        assert_eq!(
            dp_out.pod_statements[0],
            vec![0],
            "segment 1 holds just producer 0"
        );
        assert_eq!(
            dp_out.pod_statements[1],
            (1..=consumer).collect::<Vec<_>>(),
            "segment 2 holds the remaining 20 producers and the consumer T"
        );

        let full_out = partition(&input).expect("full pipeline must recover K=2");
        assert_eq!(
            full_out.pod_count, 2,
            "full pipeline relies on the DP layer to recover K=2 on this fan-in input"
        );
    }
}
