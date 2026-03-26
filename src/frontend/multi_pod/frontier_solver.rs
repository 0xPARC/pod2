//! Frontier-state recursive packing solver for multi-POD assignment.
//!
//! Searches over pod boundary interfaces rather than statement assignments.
//! See `/workspace/docs/plans/multi_pod_frontier_solver.md` for the design.

use std::collections::{BTreeSet, HashMap};

use super::{
    cost::{CustomPredicateId, StatementCost},
    deps::{DependencyGraph, ExternalDependency, StatementSource},
    solver::{MultiPodSolution, SolverInput},
    Result,
};
use crate::middleware::Params;

// ---------------------------------------------------------------------------
// Resource tracking
// ---------------------------------------------------------------------------

/// Aggregate resource usage for a set of statements, comparable against
/// per-POD capacity limits.
#[derive(Clone, Debug, Default)]
struct ResourceUsage {
    statements: usize,
    merkle_proofs: usize,
    merkle_state_transitions: usize,
    custom_pred_verifications: usize,
    signed_by: usize,
    public_key_of: usize,
    custom_predicates: BTreeSet<CustomPredicateId>,
}

impl ResourceUsage {
    fn add(&mut self, cost: &StatementCost) {
        self.statements += 1;
        self.merkle_proofs += cost.merkle_proofs;
        self.merkle_state_transitions += cost.merkle_state_transitions;
        self.custom_pred_verifications += cost.custom_pred_verifications;
        self.signed_by += cost.signed_by;
        self.public_key_of += cost.public_key_of;
        self.custom_predicates
            .extend(cost.custom_predicates_ids.iter().cloned());
    }

    fn fits(&self, params: &Params) -> bool {
        self.statements <= params.max_priv_statements()
            && self.merkle_proofs <= params.max_merkle_proofs_containers
            && self.merkle_state_transitions
                <= params.max_merkle_tree_state_transition_proofs_containers
            && self.custom_pred_verifications <= params.max_custom_predicate_verifications
            && self.signed_by <= params.max_signed_by
            && self.public_key_of <= params.max_public_key_of
            && self.custom_predicates.len() <= params.max_custom_predicates
    }

    /// Quick lower bound on pods needed for a set of resource costs.
    fn min_pods_for(
        costs: impl Iterator<Item = impl std::borrow::Borrow<StatementCost>>,
        params: &Params,
    ) -> usize {
        let mut totals = ResourceUsage::default();
        for c in costs {
            totals.add(c.borrow());
        }
        let mut min_pods = 1usize;
        min_pods = min_pods.max(totals.statements.div_ceil(params.max_priv_statements()));
        min_pods = min_pods.max(
            totals
                .merkle_proofs
                .div_ceil(params.max_merkle_proofs_containers),
        );
        if params.max_merkle_tree_state_transition_proofs_containers > 0 {
            min_pods = min_pods.max(
                totals
                    .merkle_state_transitions
                    .div_ceil(params.max_merkle_tree_state_transition_proofs_containers),
            );
        }
        if params.max_custom_predicate_verifications > 0 {
            min_pods = min_pods.max(
                totals
                    .custom_pred_verifications
                    .div_ceil(params.max_custom_predicate_verifications),
            );
        }
        if params.max_signed_by > 0 {
            min_pods = min_pods.max(totals.signed_by.div_ceil(params.max_signed_by));
        }
        if params.max_public_key_of > 0 {
            min_pods = min_pods.max(totals.public_key_of.div_ceil(params.max_public_key_of));
        }
        min_pods
    }
}

// ---------------------------------------------------------------------------
// Dependency closure
// ---------------------------------------------------------------------------

/// Compute the transitive dependency closure of a set of statements.
/// Returns all statement indices that are (transitively) required by
/// the given set, including the set itself. Only follows internal deps.
///
/// If `available` is provided, statements in that set are treated as
/// pre-satisfied boundaries: they ARE included in the closure but their
/// transitive deps are not followed. This is used by `absorb_subgraphs`
/// to compute the incremental cost of absorbing a statement.
fn closure(
    frontier: &BTreeSet<usize>,
    deps: &DependencyGraph,
    available: Option<&BTreeSet<usize>>,
) -> BTreeSet<usize> {
    let mut result = BTreeSet::new();
    let mut stack: Vec<usize> = frontier.iter().copied().collect();
    while let Some(s) = stack.pop() {
        if !result.insert(s) {
            continue;
        }
        // If this statement is available from elsewhere, don't follow its deps.
        if let Some(avail) = available {
            if avail.contains(&s) && !frontier.contains(&s) {
                continue;
            }
        }
        for dep in &deps.statement_deps[s] {
            if let StatementSource::Internal(d) = dep {
                if !result.contains(d) {
                    stack.push(*d);
                }
            }
        }
    }
    result
}

/// Find dep-free statements (no internal dependencies). Unused since
/// `absorb_subgraphs` handles re-proving for arbitrary subgraphs.
#[allow(dead_code)]
fn find_reprove_candidates(deps: &DependencyGraph) -> BTreeSet<usize> {
    let mut candidates = BTreeSet::new();
    for (i, dep_list) in deps.statement_deps.iter().enumerate() {
        let has_internal = dep_list
            .iter()
            .any(|d| matches!(d, StatementSource::Internal(_)));
        if !has_internal {
            candidates.insert(i);
        }
    }
    candidates
}

/// Compute the residual frontier: statements NOT in `local` that are
/// direct internal dependencies of statements IN `local`.
fn residual(local: &BTreeSet<usize>, deps: &DependencyGraph) -> BTreeSet<usize> {
    let mut r = BTreeSet::new();
    for &s in local {
        for dep in &deps.statement_deps[s] {
            if let StatementSource::Internal(d) = dep {
                if !local.contains(d) {
                    r.insert(*d);
                }
            }
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Re-proving: absorb R subgraphs into L to reduce parent count
// ---------------------------------------------------------------------------

/// Try to absorb statements from R (and their dependency subgraphs) into L,
/// reducing the number of parent pods needed.
///
/// This is valuable when fan-in (max_input_pods) is the binding constraint:
/// re-proving a subgraph locally is cheaper than importing it from a parent
/// if the pod has spare resource capacity.
///
/// Absorbs cheapest subgraphs first, stopping when R fits in the available
/// parent slots.
#[allow(clippy::too_many_arguments)]
fn absorb_subgraphs(
    local: &mut BTreeSet<usize>,
    r: &mut BTreeSet<usize>,
    usage: &mut ResourceUsage,
    costs: &[StatementCost],
    deps: &DependencyGraph,
    params: &Params,
    max_public: usize,
    internal_input_slots: usize,
) {
    // How many parent slots does R currently need?
    let parents_needed = r.len().div_ceil(max_public).max(1);
    if parents_needed <= internal_input_slots {
        return; // Already fits, no absorption needed.
    }

    // For each statement in R, compute its absorption cost: the full
    // subgraph (statement + transitive deps) that would need to be
    // re-proved locally, excluding statements already in L.
    let mut candidates: Vec<(usize, BTreeSet<usize>)> = Vec::new();

    for &s in r.iter() {
        // Compute the subgraph: closure of {s} minus what's already in L.
        let subgraph = closure(&[s].into(), deps, Some(local));
        let to_absorb: BTreeSet<usize> = subgraph.difference(local).copied().collect();

        if to_absorb.is_empty() {
            continue; // Already fully in L (shouldn't happen, but guard).
        }

        // Check that absorbing this subgraph doesn't introduce new external
        // pod dependencies (which would consume input slots too).
        let new_ext = to_absorb.iter().any(|&stmt| {
            deps.statement_deps[stmt]
                .iter()
                .any(|dep| matches!(dep, StatementSource::External(_)))
                && !local.contains(&stmt)
        });
        if new_ext {
            continue; // Would need additional external inputs.
        }

        candidates.push((s, to_absorb));
    }

    // Sort by total statement count (cheapest subgraph first).
    candidates.sort_by_key(|(_, subgraph)| subgraph.len());

    // Greedily absorb until R fits in available parent slots.
    for (_, subgraph) in candidates {
        let parents_needed = if r.is_empty() {
            0
        } else {
            r.len().div_ceil(max_public).max(1)
        };
        if parents_needed <= internal_input_slots {
            break; // R now fits.
        }

        // Check if absorbing fits in remaining resource budget.
        let mut trial = usage.clone();
        for &stmt in &subgraph {
            trial.add(&costs[stmt]);
        }
        if !trial.fits(params) {
            continue; // Doesn't fit.
        }

        // Absorb: move subgraph from R to L.
        for &stmt in &subgraph {
            local.insert(stmt);
            r.remove(&stmt);
        }
        *usage = trial;

        // Recompute R: absorption may have satisfied other R statements' deps.
        let new_r = residual(local, deps);
        *r = new_r;
    }
}

// ---------------------------------------------------------------------------
// L-search: local packing candidates
// ---------------------------------------------------------------------------

/// A candidate packing for a single pod.
#[derive(Clone, Debug)]
struct PackingCandidate {
    /// Statements proved locally in this pod (L).
    local: BTreeSet<usize>,
    /// Unmet dependencies that must come from parent pods (R).
    residual: BTreeSet<usize>,
}

/// Find local packing candidates for a single pod.
///
/// Currently returns a single greedy candidate. A future Pareto L-search
/// could generate multiple candidates with different resource tradeoffs,
/// but this is a quality improvement, not required for correctness.
fn l_search(
    d: &BTreeSet<usize>,
    c: &BTreeSet<usize>,
    costs: &[StatementCost],
    deps: &DependencyGraph,
    params: &Params,
) -> Vec<PackingCandidate> {
    let greedy = greedy_l(d, c, costs, deps, params);
    if let Some(candidate) = greedy {
        vec![candidate]
    } else {
        vec![]
    }
}

/// Greedy L-search: try to fit as much of the closure as possible
/// into one pod's budget.
///
/// Strategy:
/// 1. Start with D (mandatory).
/// 2. Add remaining closure statements in reverse index order (highest
///    index first). For linear chains this packs contiguous segments
///    adjacent to D, producing optimal chain splits.
/// 3. Stop adding when the budget is full.
fn greedy_l(
    d: &BTreeSet<usize>,
    c: &BTreeSet<usize>,
    costs: &[StatementCost],
    deps: &DependencyGraph,
    params: &Params,
) -> Option<PackingCandidate> {
    // Start with D (mandatory).
    let mut local: BTreeSet<usize> = d.clone();
    let mut usage = ResourceUsage::default();
    for &s in d {
        usage.add(&costs[s]);
    }

    // Remaining optional statements sorted by reverse index order.
    // For chains, this packs contiguous segments adjacent to D.
    let mut optional: Vec<usize> = c.difference(&local).copied().collect();
    optional.sort_by(|a, b| b.cmp(a)); // highest index first

    // Check that D alone fits.
    if !usage.fits(params) {
        return None; // D exceeds one pod's budget
    }

    // Greedily add optional statements.
    for &s in &optional {
        let mut trial = usage.clone();
        trial.add(&costs[s]);
        if trial.fits(params) {
            local.insert(s);
            usage = trial;
        }
    }

    let r = residual(&local, deps);
    Some(PackingCandidate { local, residual: r })
}

/// Compute per-dimension scarcity ratios for a set of statements.
/// Higher = tighter (more demand relative to capacity).
/// Unused: reserved for future Pareto L-search prioritization.
#[allow(dead_code)]
fn resource_scarcity(
    statements: &BTreeSet<usize>,
    costs: &[StatementCost],
    params: &Params,
) -> [f64; 6] {
    let mut totals = [0usize; 6];
    for &s in statements {
        let c = &costs[s];
        totals[0] += 1; // statement slot
        totals[1] += c.merkle_proofs;
        totals[2] += c.merkle_state_transitions;
        totals[3] += c.custom_pred_verifications;
        totals[4] += c.signed_by;
        totals[5] += c.public_key_of;
    }

    let caps = [
        params.max_priv_statements() as f64,
        params.max_merkle_proofs_containers as f64,
        params.max_merkle_tree_state_transition_proofs_containers as f64,
        params.max_custom_predicate_verifications as f64,
        params.max_signed_by as f64,
        params.max_public_key_of as f64,
    ];

    let mut scarcity = [0.0f64; 6];
    for i in 0..6 {
        scarcity[i] = if caps[i] > 0.0 {
            totals[i] as f64 / caps[i]
        } else if totals[i] > 0 {
            f64::INFINITY
        } else {
            0.0
        };
    }
    scarcity
}

/// Priority score for including a statement in the local set.
/// Higher = more valuable to include (consumes scarce resources,
/// reducing the burden on parent pods).
/// Unused: reserved for future Pareto L-search prioritization.
#[allow(dead_code)]
fn statement_priority(s: usize, costs: &[StatementCost], scarcity: &[f64; 6]) -> f64 {
    let c = &costs[s];
    let mut score = scarcity[0]; // 1 statement slot, weighted by slot scarcity
    score += c.merkle_proofs as f64 * scarcity[1];
    score += c.merkle_state_transitions as f64 * scarcity[2];
    score += c.custom_pred_verifications as f64 * scarcity[3];
    score += c.signed_by as f64 * scarcity[4];
    score += c.public_key_of as f64 * scarcity[5];
    score
}

// ---------------------------------------------------------------------------
// R-partition: split residual across parents
// ---------------------------------------------------------------------------

/// Generate valid partitions of residual R across ≤ max_inputs parents,
/// each receiving ≤ max_public statements.
///
/// Uses output-path affinity: statements in R that serve the same D
/// statements (i.e., the same D statements transitively depend on them)
/// are grouped together. This naturally co-locates external pod
/// dependencies and keeps dependency chains intact.
///
/// Returns a list of partitions, where each partition is a Vec of Frontiers
/// (one per parent pod).
fn partition_residual(
    r: &BTreeSet<usize>,
    max_inputs: usize,
    max_public: usize,
    d: &BTreeSet<usize>,
    local: &BTreeSet<usize>,
    deps: &DependencyGraph,
) -> Vec<Vec<BTreeSet<usize>>> {
    if r.is_empty() {
        return vec![vec![]]; // no parents needed
    }

    if r.len() <= max_public {
        // Fits in one parent.
        return vec![vec![r.clone()]];
    }

    if max_inputs < 2 {
        return vec![];
    }

    // Compute affinity groups: which D statements does each R statement serve?
    let affinities = compute_affinities(r, d, local, deps);

    // Group R statements by their affinity set.
    let mut affinity_groups: HashMap<Vec<usize>, BTreeSet<usize>> = HashMap::new();
    for &s in r {
        let key = affinities
            .get(&s)
            .map(|set| set.iter().copied().collect::<Vec<_>>())
            .unwrap_or_default();
        affinity_groups.entry(key).or_default().insert(s);
    }

    let groups: Vec<BTreeSet<usize>> = affinity_groups.into_values().collect();

    let mut partitions = Vec::new();

    // Greedy affinity merge: try to merge groups into ≤ max_inputs partitions.
    if let Some(partition) = merge_affinity_groups(&groups, max_inputs, max_public) {
        partitions.push(partition);
    }

    // Complete fallback for max_inputs == 2: bitmask enumeration of bipartitions.
    // This ensures we don't declare infeasible when the greedy merge fails but
    // a valid partition exists, and also explores alternatives when the greedy
    // merge succeeds but leads to recursive failure.
    if max_inputs == 2 {
        let items: Vec<usize> = r.iter().copied().collect();
        let n = items.len();
        if n <= 16 && r.len() <= max_public * max_inputs {
            let min_first = n.saturating_sub(max_public);
            let max_first = max_public.min(n);

            for mask in 0u32..(1u32 << n) {
                let count = mask.count_ones() as usize;
                if count < min_first || count > max_first {
                    continue;
                }
                let mut a = BTreeSet::new();
                let mut b = BTreeSet::new();
                for (i, &item) in items.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        a.insert(item);
                    } else {
                        b.insert(item);
                    }
                }
                // Symmetry breaking: first set has the smallest element.
                if !a.is_empty() && !b.is_empty() && a.first() > b.first() {
                    continue;
                }
                let candidate = vec![a, b];
                // Skip if this duplicates the greedy result.
                if !partitions.contains(&candidate) {
                    partitions.push(candidate);
                }
            }
        }
    }

    // For max_inputs > 2 without bitmask, the greedy merge is all we have.
    // This is sufficient for practical cases (max_input_pods is typically 2).

    partitions
}

/// For each statement in R, compute which D statements transitively depend
/// on it (walking through L only, not through other R statements).
fn compute_affinities(
    r: &BTreeSet<usize>,
    d: &BTreeSet<usize>,
    local: &BTreeSet<usize>,
    deps: &DependencyGraph,
) -> HashMap<usize, BTreeSet<usize>> {
    let mut affinity: HashMap<usize, BTreeSet<usize>> = HashMap::new();

    for &d_stmt in d {
        // Walk deps of d_stmt within local, collecting R statements reached.
        let mut visited = BTreeSet::new();
        let mut stack = vec![d_stmt];
        while let Some(s) = stack.pop() {
            if !visited.insert(s) {
                continue;
            }
            for dep in &deps.statement_deps[s] {
                if let StatementSource::Internal(idx) = dep {
                    if r.contains(idx) {
                        affinity.entry(*idx).or_default().insert(d_stmt);
                    } else if local.contains(idx) && !visited.contains(idx) {
                        stack.push(*idx);
                    }
                }
            }
        }
    }

    affinity
}

/// Merge affinity groups into ≤ max_parts partitions, each ≤ max_per_part.
/// Greedy: sort groups largest-first, assign each to the smallest partition
/// that still has room.
fn merge_affinity_groups(
    groups: &[BTreeSet<usize>],
    max_parts: usize,
    max_per_part: usize,
) -> Option<Vec<BTreeSet<usize>>> {
    let mut sorted: Vec<&BTreeSet<usize>> = groups.iter().collect();
    sorted.sort_by_key(|s| std::cmp::Reverse(s.len()));

    let mut partitions: Vec<BTreeSet<usize>> = Vec::new();

    for group in sorted {
        // Try to add to an existing partition with room.
        let mut placed = false;
        // Sort by size ascending to fill smallest first.
        let mut best_idx = None;
        let mut best_size = usize::MAX;
        for (i, part) in partitions.iter().enumerate() {
            if part.len() + group.len() <= max_per_part && part.len() < best_size {
                best_size = part.len();
                best_idx = Some(i);
            }
        }
        if let Some(i) = best_idx {
            partitions[i].extend(group.iter().copied());
            placed = true;
        }
        if !placed {
            if partitions.len() >= max_parts {
                return None; // Can't fit
            }
            if group.len() > max_per_part {
                return None; // Single group too large
            }
            partitions.push(group.clone());
        }
    }

    // Remove empty partitions.
    partitions.retain(|p| !p.is_empty());
    Some(partitions)
}

// ---------------------------------------------------------------------------
// Recursive solver
// ---------------------------------------------------------------------------

/// Memoization key: (sorted frontier statement indices, k_budget).
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct MemoKey {
    frontier: Vec<usize>,
    k_budget: usize,
}

/// A pod in the solution DAG.
#[derive(Clone, Debug)]
struct PodNode {
    /// Statement indices proved in this pod.
    statements: Vec<usize>,
    /// Statement indices that are public in this pod.
    public_statements: BTreeSet<usize>,
    /// Indices into the solution's pod list for internal input pods.
    internal_inputs: Vec<usize>,
}

/// Result of packing a frontier into pods.
#[derive(Clone, Debug)]
struct PackResult {
    /// Pods in topological order (earliest first, this pod last).
    pods: Vec<PodNode>,
}

/// Solve the packing problem using frontier-state recursive search.
pub fn solve(input: &SolverInput) -> Result<MultiPodSolution> {
    if input.output_public_indices.is_empty() {
        return Err(super::Error::Solver(
            "No public statements requested.".to_string(),
        ));
    }

    let num_output_public = input.output_public_indices.len();
    if num_output_public > input.params.max_public_statements {
        return Err(super::Error::Solver(format!(
            "Too many public statements: {} > {}",
            num_output_public, input.params.max_public_statements
        )));
    }

    // The output pod's export obligations.
    let output_frontier: BTreeSet<usize> = input.output_public_indices.iter().copied().collect();

    // Incremental k: try k=1, 2, 3, ...
    for k in 1..=input.max_pods {
        let mut memo: HashMap<MemoKey, Option<PackResult>> = HashMap::new();
        if let Some(result) = pack_pod(&output_frontier, k, input, &mut memo) {
            let solution = convert_to_solution(result, input);
            #[cfg(test)]
            {
                let errors = solution.validate(input);
                assert!(
                    errors.is_empty(),
                    "frontier solver produced invalid solution:\n{}",
                    errors.join("\n")
                );
            }
            return Ok(solution);
        }
    }

    Err(super::Error::Solver(format!(
        "No feasible solution found with up to {} PODs",
        input.max_pods
    )))
}

/// Recursively pack a pod and its ancestors.
///
/// - `d`: statements this pod must export (make public). For the output
///   pod this is the user's public set; for intermediate pods it's the
///   partition element assigned by the parent.
/// - `k_budget`: maximum pods available (including this one).
/// - `input`: the full problem input.
/// - `memo`: memoization table keyed by (D, k_budget).
///
/// Returns Some(PackResult) if feasible, None if not.
fn pack_pod(
    d: &BTreeSet<usize>,
    k_budget: usize,
    input: &SolverInput,
    memo: &mut HashMap<MemoKey, Option<PackResult>>,
) -> Option<PackResult> {
    if k_budget == 0 {
        return None;
    }

    // Check memo.
    let key = MemoKey {
        frontier: d.iter().copied().collect(),
        k_budget,
    };
    if let Some(cached) = memo.get(&key) {
        return cached.clone();
    }

    // Compute closure of D.
    let c = closure(d, input.deps, None);

    // Quick lower bound: if the closure needs more pods than we have, fail.
    let closure_costs = c.iter().map(|&s| &input.costs[s]);
    let min_pods = ResourceUsage::min_pods_for(closure_costs, input.params);
    if min_pods > k_budget {
        memo.insert(key, None);
        return None;
    }

    // Find L candidates.
    let candidates = l_search(d, &c, input.costs, input.deps, input.params);
    let max_pub = input.params.max_public_statements;

    for candidate in &candidates {
        // --- Input slot budget ---
        // Compute how many internal parent slots the residual requires.
        // This drives both external trimming and D-splitting.
        let min_internal = if candidate.residual.is_empty() {
            0
        } else {
            candidate.residual.len().div_ceil(max_pub).max(1)
        };

        // How many external pod slots we can afford.
        let max_ext = input.params.max_input_pods.saturating_sub(min_internal);

        // --- Trim external overflow from L (non-D statements) ---
        let (local, r) = trim_external_overflow(
            &candidate.local,
            &candidate.residual,
            d,
            input.deps,
            max_ext,
        );

        // --- D-splitting ---
        // If external deps in D would still overflow after trimming,
        // forward excess D statements through parent pods.
        let ext_in_local = count_external_pods(&local, input.deps);
        let ext_in_d = collect_external_pods(d, input.deps);
        let min_internal_post = if r.is_empty() {
            0
        } else {
            r.len().div_ceil(max_pub).max(1)
        };

        let d_forward = if !r.is_empty()
            && ext_in_local + min_internal_post > input.params.max_input_pods
            && !ext_in_d.is_empty()
        {
            let target_ext = input
                .params
                .max_input_pods
                .saturating_sub(min_internal_post);
            let (_, d_fwd) = split_external_deps(d, input.deps, target_ext);
            d_fwd
        } else {
            BTreeSet::new()
        };

        // Apply D-split: remove forwarded statements from local, add to R.
        let (local, r) = if !d_forward.is_empty() {
            let mut new_local = local;
            let mut new_r = r;
            for &s in &d_forward {
                new_local.remove(&s);
                new_r.insert(s);
            }
            // Remove orphaned statements no longer needed by any local stmt.
            let needed: BTreeSet<usize> = new_local
                .iter()
                .flat_map(|&s| {
                    input.deps.statement_deps[s]
                        .iter()
                        .filter_map(|dep| match dep {
                            StatementSource::Internal(idx) => Some(*idx),
                            _ => None,
                        })
                })
                .collect();
            let orphans: Vec<usize> = new_local
                .iter()
                .filter(|&&s| !d.contains(&s) && !needed.contains(&s))
                .copied()
                .collect();
            for s in orphans {
                new_local.remove(&s);
            }
            // Recompute residual for trimmed local.
            for &s in &new_local {
                for dep in &input.deps.statement_deps[s] {
                    if let StatementSource::Internal(idx) = dep {
                        if !new_local.contains(idx) {
                            new_r.insert(*idx);
                        }
                    }
                }
            }
            (new_local, new_r)
        } else {
            (local, r)
        };

        let d_local: BTreeSet<usize> = d.difference(&d_forward).copied().collect();
        let mut local = local;
        let mut r = r;

        // --- Final slot computation ---
        let ext_pods_needed = count_external_pods(&local, input.deps);
        let internal_input_slots = input.params.max_input_pods.saturating_sub(ext_pods_needed);

        // --- Re-proving: absorb cheap R subgraphs to reduce parent count ---
        if !r.is_empty() && internal_input_slots > 0 {
            let mut usage = ResourceUsage::default();
            for &s in &local {
                usage.add(&input.costs[s]);
            }
            absorb_subgraphs(
                &mut local,
                &mut r,
                &mut usage,
                input.costs,
                input.deps,
                input.params,
                max_pub,
                internal_input_slots,
            );
        }

        // --- Base case: everything fits in this pod ---
        if r.is_empty() {
            let result = PackResult {
                pods: vec![PodNode {
                    statements: local.iter().copied().collect(),
                    public_statements: d.clone(),
                    internal_inputs: vec![],
                }],
            };
            memo.insert(key, Some(result.clone()));
            return Some(result);
        }

        // Prune: infeasible if no internal parent slots available.
        if internal_input_slots == 0 {
            continue;
        }

        // --- Partition R and recurse ---
        let partitions = partition_residual(
            &r,
            internal_input_slots,
            max_pub,
            &d_local,
            &local,
            input.deps,
        );

        for partition in &partitions {
            let mut parent_pods: Vec<PodNode> = Vec::new();
            let mut parent_pod_counts: Vec<usize> = Vec::new();
            let mut feasible = true;

            for parent_d in partition {
                if parent_d.is_empty() {
                    continue;
                }
                let parent_k = k_budget - 1 - parent_pods.len();
                if parent_k == 0 {
                    feasible = false;
                    break;
                }
                match pack_pod(parent_d, parent_k, input, memo) {
                    Some(mut parent_result) => {
                        parent_pod_counts.push(parent_result.pods.len());
                        parent_pods.append(&mut parent_result.pods);
                    }
                    None => {
                        feasible = false;
                        break;
                    }
                }
            }

            if feasible {
                let mut parent_indices = Vec::new();
                let mut offset = 0;
                for &count in &parent_pod_counts {
                    parent_indices.push(offset + count - 1);
                    offset += count;
                }

                let mut all_pods = parent_pods;
                all_pods.push(PodNode {
                    statements: local.iter().copied().collect(),
                    public_statements: d.clone(),
                    internal_inputs: parent_indices,
                });

                let result = PackResult { pods: all_pods };
                memo.insert(key, Some(result.clone()));
                return Some(result);
            }
        }
    }

    memo.insert(key, None);
    None
}

/// When L references more external pods than `max_ext_allowed` input slots,
/// move non-D statements with excess external deps from L to R so a parent
/// pod can forward them.
///
/// `max_ext_allowed` is the caller's budget for external pod input slots
/// (typically `max_input_pods - min_internal_parents`).
///
/// Keeps external pods referenced by D statements (mandatory) and the
/// most-referenced external pods up to the budget.
fn trim_external_overflow(
    local: &BTreeSet<usize>,
    residual: &BTreeSet<usize>,
    d: &BTreeSet<usize>,
    deps: &DependencyGraph,
    max_ext_allowed: usize,
) -> (BTreeSet<usize>, BTreeSet<usize>) {
    // Find which external pods each statement in L needs.
    let mut ext_pod_users: HashMap<crate::middleware::Hash, Vec<usize>> = HashMap::new();
    let mut mandatory_ext_pods = BTreeSet::new();

    for &s in local {
        for dep in &deps.statement_deps[s] {
            if let StatementSource::External(ext) = dep {
                ext_pod_users.entry(ext.pod_hash).or_default().push(s);
                if d.contains(&s) {
                    mandatory_ext_pods.insert(ext.pod_hash);
                }
            }
        }
    }

    let total_ext = ext_pod_users.len();

    if total_ext <= max_ext_allowed {
        return (local.clone(), residual.clone());
    }

    // Too many external pods. Keep mandatory ones + highest-use ones.
    let mut ext_pods_ranked: Vec<(crate::middleware::Hash, usize, bool)> = ext_pod_users
        .iter()
        .map(|(hash, users)| (*hash, users.len(), mandatory_ext_pods.contains(hash)))
        .collect();
    // Sort: mandatory first, then by number of users descending.
    ext_pods_ranked.sort_by(|a, b| {
        b.2.cmp(&a.2) // mandatory first
            .then(b.1.cmp(&a.1)) // then most users
    });

    let kept_ext_pods: BTreeSet<crate::middleware::Hash> = ext_pods_ranked
        .iter()
        .take(max_ext_allowed)
        .map(|(h, _, _)| *h)
        .collect();

    // Move statements with excluded external deps from L to R.
    let mut new_local = BTreeSet::new();
    let mut new_residual = residual.clone();

    for &s in local {
        let needs_excluded_ext = deps.statement_deps[s].iter().any(|dep| {
            if let StatementSource::External(ext) = dep {
                !kept_ext_pods.contains(&ext.pod_hash)
            } else {
                false
            }
        });

        if needs_excluded_ext && !d.contains(&s) {
            // Move to residual — a parent pod will handle this.
            new_residual.insert(s);
        } else {
            new_local.insert(s);
        }
    }

    // Recompute residual: add any deps of new_local that aren't in new_local.
    for &s in &new_local {
        for dep in &deps.statement_deps[s] {
            if let StatementSource::Internal(d_idx) = dep {
                if !new_local.contains(d_idx) {
                    new_residual.insert(*d_idx);
                }
            }
        }
    }

    (new_local, new_residual)
}

/// Collect distinct external pod hashes referenced by a set of statements.
fn collect_external_pods(
    stmts: &BTreeSet<usize>,
    deps: &DependencyGraph,
) -> BTreeSet<crate::middleware::Hash> {
    let mut result = BTreeSet::new();
    for &s in stmts {
        for dep in &deps.statement_deps[s] {
            if let StatementSource::External(ext) = dep {
                result.insert(ext.pod_hash);
            }
        }
    }
    result
}

/// Split D into (d_local, d_forward) based on external dep overflow.
/// Keeps statements whose external pods fit within max_ext_slots in d_local.
/// Moves the rest to d_forward (to be proved by a parent pod).
fn split_external_deps(
    d: &BTreeSet<usize>,
    deps: &DependencyGraph,
    max_ext_slots: usize,
) -> (BTreeSet<usize>, BTreeSet<usize>) {
    // Count how many D statements use each external pod.
    let mut ext_pod_users: HashMap<crate::middleware::Hash, Vec<usize>> = HashMap::new();
    let mut no_ext: Vec<usize> = Vec::new();

    for &s in d {
        let mut has_ext = false;
        for dep in &deps.statement_deps[s] {
            if let StatementSource::External(ext) = dep {
                ext_pod_users.entry(ext.pod_hash).or_default().push(s);
                has_ext = true;
            }
        }
        if !has_ext {
            no_ext.push(s);
        }
    }

    // Rank external pods by number of D statements that use them.
    let mut ranked: Vec<(crate::middleware::Hash, usize)> = ext_pod_users
        .iter()
        .map(|(h, users)| (*h, users.len()))
        .collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1)); // most users first

    let kept: BTreeSet<crate::middleware::Hash> =
        ranked.iter().take(max_ext_slots).map(|(h, _)| *h).collect();

    let mut d_local: BTreeSet<usize> = no_ext.into_iter().collect();
    let mut d_forward = BTreeSet::new();

    for &s in d {
        let uses_excluded = deps.statement_deps[s].iter().any(|dep| {
            if let StatementSource::External(ext) = dep {
                !kept.contains(&ext.pod_hash)
            } else {
                false
            }
        });
        if uses_excluded {
            d_forward.insert(s);
        } else {
            d_local.insert(s);
        }
    }

    (d_local, d_forward)
}

/// Count distinct external pods referenced by statements in the local set.
fn count_external_pods(local: &BTreeSet<usize>, deps: &DependencyGraph) -> usize {
    let mut external_pods = BTreeSet::new();
    for &s in local {
        for dep in &deps.statement_deps[s] {
            if let StatementSource::External(ext) = dep {
                external_pods.insert(ext.pod_hash);
            }
        }
    }
    external_pods.len()
}

// ---------------------------------------------------------------------------
// Solution conversion
// ---------------------------------------------------------------------------

/// Convert the internal PackResult into the MultiPodSolution expected
/// by SolvedMultiPod::prove().
fn convert_to_solution(result: PackResult, input: &SolverInput) -> MultiPodSolution {
    let pod_count = result.pods.len();
    let n = input.num_statements;

    let mut statement_to_pods: Vec<Vec<usize>> = vec![vec![]; n];
    let mut pod_statements: Vec<Vec<usize>> = Vec::with_capacity(pod_count);
    let mut pod_public_statements: Vec<BTreeSet<usize>> = Vec::with_capacity(pod_count);
    let mut pod_internal_inputs: Vec<BTreeSet<usize>> = Vec::with_capacity(pod_count);

    // Collect external pod info from dependencies.
    let mut external_pod_hashes: Vec<crate::middleware::Hash> = Vec::new();
    let mut external_pod_to_idx: HashMap<crate::middleware::Hash, usize> = HashMap::new();
    let mut external_premises: Vec<ExternalDependency> = Vec::new();
    let mut external_premise_to_idx: HashMap<ExternalDependency, usize> = HashMap::new();

    for dep_list in &input.deps.statement_deps {
        for dep in dep_list {
            if let StatementSource::External(ext) = dep {
                external_pod_to_idx.entry(ext.pod_hash).or_insert_with(|| {
                    external_pod_hashes.push(ext.pod_hash);
                    external_pod_hashes.len() - 1
                });
                external_premise_to_idx
                    .entry(ext.clone())
                    .or_insert_with(|| {
                        external_premises.push(ext.clone());
                        external_premises.len() - 1
                    });
            }
        }
    }

    let mut pod_external_inputs: Vec<BTreeSet<usize>> = Vec::with_capacity(pod_count);
    let mut pod_public_external_premises: Vec<BTreeSet<usize>> = Vec::with_capacity(pod_count);

    for (p, pod) in result.pods.iter().enumerate() {
        pod_statements.push(pod.statements.clone());
        pod_public_statements.push(pod.public_statements.clone());
        pod_internal_inputs.push(pod.internal_inputs.iter().copied().collect());

        for &s in &pod.statements {
            statement_to_pods[s].push(p);
        }

        // Track external inputs for this pod.
        let mut ext_inputs = BTreeSet::new();
        for &s in &pod.statements {
            for dep in &input.deps.statement_deps[s] {
                if let StatementSource::External(ext) = dep {
                    if let Some(&idx) = external_pod_to_idx.get(&ext.pod_hash) {
                        ext_inputs.insert(idx);
                    }
                }
            }
        }
        pod_external_inputs.push(ext_inputs);

        pod_public_external_premises.push(BTreeSet::new());
    }

    // Populate pod_public_external_premises: when a non-output pod imports
    // an external pod and has a child that does NOT import that same external
    // pod, forward the external premises so the child can access them.
    for p in 0..pod_count {
        // Find children of pod p.
        let has_child = (0..pod_count).any(|c| result.pods[c].internal_inputs.contains(&p));
        if !has_child {
            continue; // Output pod or leaf, no forwarding needed.
        }

        for &ext_pod_idx in &pod_external_inputs[p] {
            let ext_hash = external_pod_hashes[ext_pod_idx];

            // Check if any child does NOT import this external pod directly.
            let child_needs_forward = (0..pod_count)
                .filter(|&c| result.pods[c].internal_inputs.contains(&p))
                .any(|c| !pod_external_inputs[c].contains(&ext_pod_idx));

            if child_needs_forward {
                // Forward all premises from this external pod.
                for (prem_idx, prem) in external_premises.iter().enumerate() {
                    if prem.pod_hash == ext_hash {
                        pod_public_external_premises[p].insert(prem_idx);
                    }
                }
            }
        }
    }

    MultiPodSolution {
        pod_count,
        statement_to_pods,
        pod_statements,
        pod_public_statements,
        pod_internal_inputs,
        external_pod_hashes,
        pod_external_inputs,
        external_premises,
        pod_public_external_premises,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_costs(n: usize, merkle: &[usize]) -> Vec<StatementCost> {
        (0..n)
            .map(|i| {
                let mut c = StatementCost::default();
                if let Some(&m) = merkle.get(i) {
                    c.merkle_proofs = m;
                }
                c
            })
            .collect()
    }

    fn make_chain_deps(n: usize) -> DependencyGraph {
        let mut statement_deps = Vec::with_capacity(n);
        statement_deps.push(vec![]); // s0 has no deps
        for i in 1..n {
            statement_deps.push(vec![StatementSource::Internal(i - 1)]);
        }
        DependencyGraph { statement_deps }
    }

    #[test]
    fn test_closure_chain() {
        let deps = make_chain_deps(5);
        let frontier: BTreeSet<usize> = [4].into();
        let c = closure(&frontier, &deps, None);
        assert_eq!(c, (0..5).collect::<BTreeSet<_>>());
    }

    #[test]
    fn test_closure_partial() {
        let deps = make_chain_deps(5);
        let frontier: BTreeSet<usize> = [2].into();
        let c = closure(&frontier, &deps, None);
        assert_eq!(c, (0..3).collect::<BTreeSet<_>>());
    }

    #[test]
    fn test_residual_chain() {
        let deps = make_chain_deps(5);
        let local: BTreeSet<usize> = [3, 4].into();
        let r = residual(&local, &deps);
        assert_eq!(r, [2].into());
    }

    #[test]
    fn test_l_search_everything_fits() {
        let costs = make_costs(3, &[1, 1, 0]);
        let deps = make_chain_deps(3);
        let params = Params::default();

        let d: BTreeSet<usize> = [2].into();
        let c = closure(&d, &deps, None);
        let candidates = l_search(&d, &c, &costs, &deps, &params);

        assert!(!candidates.is_empty());
        let best = &candidates[0];
        // Everything should fit in one pod.
        assert!(best.residual.is_empty());
        assert!(best.local.contains(&0));
        assert!(best.local.contains(&1));
        assert!(best.local.contains(&2));
    }

    #[test]
    fn test_l_search_must_overflow() {
        // 5 statements each costing 1 merkle proof, limit is 3.
        let costs = make_costs(5, &[1, 1, 1, 1, 1]);
        let deps = make_chain_deps(5);
        let params = Params {
            max_merkle_proofs_containers: 3,
            ..Params::default()
        };

        let d: BTreeSet<usize> = [4].into();
        let c = closure(&d, &deps, None);
        let candidates = l_search(&d, &c, &costs, &deps, &params);

        assert!(!candidates.is_empty());
        let best = &candidates[0];
        // Can fit at most 3 merkle proofs, so at least 2 must overflow.
        assert!(best.local.len() <= 3);
        assert!(!best.residual.is_empty());
        assert!(best.local.contains(&4)); // d must be in local
    }

    #[test]
    fn test_partition_single_parent() {
        let r: BTreeSet<usize> = [0, 1, 2].into();
        let d = BTreeSet::new();
        let local = BTreeSet::new();
        let deps = DependencyGraph {
            statement_deps: vec![vec![]; 3],
        };
        let parts = partition_residual(&r, 2, 8, &d, &local, &deps);
        // Should have at least the single-parent option.
        assert!(parts.iter().any(|p| p.len() == 1 && p[0] == r));
    }

    #[test]
    fn test_partition_needs_two_parents() {
        let r: BTreeSet<usize> = (0..10).collect();
        let d = BTreeSet::new();
        let local = BTreeSet::new();
        let deps = DependencyGraph {
            statement_deps: vec![vec![]; 10],
        };
        let parts = partition_residual(&r, 2, 8, &d, &local, &deps);
        // All partitions should have 2 parents, each ≤ 8.
        assert!(!parts.is_empty());
        for p in &parts {
            assert_eq!(p.len(), 2);
            assert!(p[0].len() <= 8);
            assert!(p[1].len() <= 8);
            let union: BTreeSet<usize> = p[0].union(&p[1]).copied().collect();
            assert_eq!(union, r);
        }
    }

    #[test]
    fn test_partition_impossible() {
        let r: BTreeSet<usize> = (0..20).collect();
        let d = BTreeSet::new();
        let local = BTreeSet::new();
        let deps = DependencyGraph {
            statement_deps: vec![vec![]; 20],
        };
        let parts = partition_residual(&r, 2, 8, &d, &local, &deps);
        assert!(parts.is_empty()); // 20 > 2*8
    }

    #[test]
    fn test_solve_single_pod() {
        let costs = make_costs(3, &[1, 1, 0]);
        let deps = make_chain_deps(3);
        let params = Params::default();

        let input = SolverInput {
            num_statements: 3,
            costs: &costs,
            deps: &deps,
            output_public_indices: &[2],
            params: &params,
            max_pods: 10,
        };

        let solution = solve(&input).unwrap();
        assert_eq!(solution.pod_count, 1);
        assert!(solution.pod_statements[0].contains(&0));
        assert!(solution.pod_statements[0].contains(&1));
        assert!(solution.pod_statements[0].contains(&2));
    }

    #[test]
    fn test_solve_independent_stmts_only_reachable_packed() {
        // 8 independent statements (no deps), limit 4 merkle proofs per pod.
        // Output public is s7 (0 merkle cost, no deps).
        // The frontier solver only packs closure(D) = {7}, so 1 pod suffices.
        // (Unreachable statements s0-s6 are ignored.)
        let costs = make_costs(8, &[1, 1, 1, 1, 1, 1, 1, 0]);
        let deps = DependencyGraph {
            statement_deps: vec![vec![]; 8],
        };
        let params = Params {
            max_merkle_proofs_containers: 4,
            ..Params::default()
        };

        let input = SolverInput {
            num_statements: 8,
            costs: &costs,
            deps: &deps,
            output_public_indices: &[7],
            params: &params,
            max_pods: 10,
        };

        let solution = solve(&input).unwrap();
        assert_eq!(solution.pod_count, 1);
    }

    #[test]
    fn test_solve_chain_needs_split() {
        // Chain: 0 -> 1 -> 2 -> 3 -> 4 -> 5 (output public)
        // 5 merkle proofs (s0-s4), limit 4 per pod.
        // Greedy packs output pod with {2,3,4,5} (4 merkle), residual {1}.
        // Parent proves {0,1}, makes 1 public. 2 pods total.
        let costs = make_costs(6, &[1, 1, 1, 1, 1, 0]);
        let deps = make_chain_deps(6);
        let params = Params {
            max_merkle_proofs_containers: 4,
            ..Params::default()
        };

        let input = SolverInput {
            num_statements: 6,
            costs: &costs,
            deps: &deps,
            output_public_indices: &[5],
            params: &params,
            max_pods: 10,
        };

        let solution = solve(&input).unwrap();
        assert!(
            solution.pod_count >= 2 && solution.pod_count <= 3,
            "Expected 2-3 pods, got {}",
            solution.pod_count
        );
    }

    #[test]
    fn test_greedy_l_suboptimal_multi_resource() {
        // Demonstrates the Pareto L-search gap: the greedy picks s2 (which
        // costs both merkle=1 AND cpv=1), filling both resource dimensions.
        // This prevents s0 (merkle-only) and s1 (cpv-only) from fitting,
        // creating R={0,1} which exceeds max_public=1 for the single parent.
        //
        // Optimal L={3,0,1} packs both single-resource statements, leaving
        // R={2} which fits in 1 parent. The greedy misses this.
        //
        // This test documents the gap; it currently fails (reports infeasible).
        let n = 4;
        let costs: Vec<StatementCost> = vec![
            StatementCost {
                merkle_proofs: 1,
                ..StatementCost::default()
            }, // s0: merkle only
            StatementCost {
                custom_pred_verifications: 1,
                ..StatementCost::default()
            }, // s1: cpv only
            StatementCost {
                merkle_proofs: 1,
                custom_pred_verifications: 1,
                ..StatementCost::default()
            }, // s2: both
            StatementCost::default(), // s3: output
        ];
        let deps = DependencyGraph {
            statement_deps: vec![
                vec![],
                vec![],
                vec![],
                vec![
                    StatementSource::Internal(0),
                    StatementSource::Internal(1),
                    StatementSource::Internal(2),
                ],
            ],
        };
        let params = Params {
            max_statements: 4,        // max_priv = 4 - 1 = 3
            max_public_statements: 1, // only 1 public per pod
            max_merkle_proofs_containers: 1,
            max_custom_predicate_verifications: 1,
            max_input_pods: 1,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };

        let input = SolverInput {
            num_statements: n,
            costs: &costs,
            deps: &deps,
            output_public_indices: &[3],
            params: &params,
            max_pods: 10,
        };

        // This SHOULD find a 2-pod solution: L={3,0,1}, parent proves {2}.
        // Currently fails because the greedy picks L={3,2} instead.
        let result = solve(&input);
        assert!(
            result.is_err(),
            "Expected infeasible (greedy L-search gap) but got {} pods. \
             If this passes, the Pareto L-search or an equivalent fix was implemented!",
            result.as_ref().unwrap().pod_count
        );
    }

    #[test]
    fn test_solve_fan_in_absorption() {
        // 3 independent branches converge on the output pod.
        // Each branch is a short chain of 2 statements (cheap to re-prove).
        // max_input_pods = 2, so the output can only have 2 parents.
        // Without absorption: needs 4 pods (3 parents + 1 output), infeasible
        //   with max_input_pods=2.
        // With absorption: the cheapest branch is re-proved in the output pod,
        //   reducing parents to 2 → feasible.
        //
        //   s0 → s1 (branch A)
        //   s2 → s3 (branch B)
        //   s4 → s5 (branch C, cheap — will be absorbed)
        //   s6 = output (depends on s1, s3, s5)
        //
        // All statements cost 1 merkle proof. Limit 6 merkle proofs per pod
        // (tight enough that not all 7 fit in one pod).
        let n = 7;
        let costs = make_costs(n, &[1, 1, 1, 1, 1, 1, 0]);
        let deps = DependencyGraph {
            statement_deps: vec![
                vec![],                             // s0: root of branch A
                vec![StatementSource::Internal(0)], // s1: depends on s0
                vec![],                             // s2: root of branch B
                vec![StatementSource::Internal(2)], // s3: depends on s2
                vec![],                             // s4: root of branch C
                vec![StatementSource::Internal(4)], // s5: depends on s4
                vec![
                    // s6: output, depends on tips
                    StatementSource::Internal(1),
                    StatementSource::Internal(3),
                    StatementSource::Internal(5),
                ],
            ],
        };
        let params = Params {
            max_merkle_proofs_containers: 6,
            max_input_pods: 2,
            ..Params::default()
        };

        let input = SolverInput {
            num_statements: n,
            costs: &costs,
            deps: &deps,
            output_public_indices: &[6],
            params: &params,
            max_pods: 10,
        };

        let solution = solve(&input).unwrap();
        // With absorption: output pod absorbs one branch (2 stmts) locally,
        // imports the other two branches from 2 parents. Should need ≤ 3 pods.
        assert!(
            solution.pod_count <= 3,
            "Expected ≤ 3 pods with fan-in absorption, got {}",
            solution.pod_count
        );
    }
}
