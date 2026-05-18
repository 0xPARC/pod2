//! Test-only MILP oracle for the multi-POD partitioner.
//!
//! Used by the DP-vs-MILP parity sweep to assert that whenever the MILP
//! finds a feasible partition, the DP does too. The MILP is never invoked
//! from production paths.
//!
//! Modelled on `src/lang/frontend_ast_split_milp.rs`. Variables:
//! - `assign[s][p]`: binary, each statement assigned to exactly one POD.
//! - `import_from[d][p]`: binary, statement `d` is imported into POD `p`
//!   (`d` produced earlier and either consumed by some statement in `p`
//!   or is an output-public statement and `p` is the output POD).
//! - `ext_import_from[e_prem][p]`: binary, external premise `e_prem` is
//!   imported into POD `p` (some statement in `p` names it).
//! - `ext_used[e][p]`: binary, POD `p` references external pod `e`.
//! - `cp_used[b][p]`: binary, POD `p` uses custom predicate `b`.
//! - `uses_chain[p]`: binary, POD `p` consumes at least one chain-tree
//!   import (which costs an input-pod slot 0).
//!
//! Constraints encode topological precedence, multi-dim per-POD resource
//! caps, the input-pod cap, and the output-POD availability for
//! output-publics.

#![allow(clippy::needless_range_loop)]

use std::collections::{BTreeSet, HashSet};

use good_lp::{
    constraint, solvers::scip::SCIPProblem, variable, Expression, ProblemVariables, Solution,
    SolverModel, Variable,
};

use super::{
    cost::{CustomPredicateId, ResourceTotals},
    shape::{AbstractDep, InputShape, OutputShape},
};

const SOLVER_BINARY_THRESHOLD: f64 = 0.5;
const SCIP_RANDOM_SEED: i32 = 0;
/// Per-call wall-clock budget for the SCIP solver. Generous enough that
/// the parity sweep (n <= 16) never approaches it, but bounded so an
/// ad-hoc call on a hard instance (e.g. cracked-refinery at fixed K)
/// returns rather than running indefinitely. A timeout surfaces as
/// `None` from `solve_for_k`, indistinguishable from "infeasible";
/// callers that need to distinguish should pick a budget that's clearly
/// longer than any feasible MILP would take.
const SCIP_TIME_LIMIT_SECONDS: f64 = 600.0;

struct MilpVars {
    n: usize,
    k: usize,
    num_ext_pods: usize,
    num_ext_premises: usize,
    num_cps: usize,
    assign: Vec<Vec<Variable>>,
    import_from: Vec<Vec<Variable>>,
    ext_import_from: Vec<Vec<Variable>>,
    ext_used: Vec<Vec<Variable>>,
    cp_used: Vec<Vec<Variable>>,
    uses_chain: Vec<Variable>,
}

fn mk_binary_grid(vars: &mut ProblemVariables, rows: usize, cols: usize) -> Vec<Vec<Variable>> {
    (0..rows)
        .map(|_| (0..cols).map(|_| vars.add(variable().binary())).collect())
        .collect()
}

fn declare_vars(
    vars: &mut ProblemVariables,
    n: usize,
    k: usize,
    num_ext_pods: usize,
    num_ext_premises: usize,
    num_cps: usize,
) -> MilpVars {
    MilpVars {
        n,
        k,
        num_ext_pods,
        num_ext_premises,
        num_cps,
        assign: mk_binary_grid(vars, n, k),
        import_from: mk_binary_grid(vars, n, k),
        ext_import_from: mk_binary_grid(vars, num_ext_premises, k),
        ext_used: mk_binary_grid(vars, num_ext_pods, k),
        cp_used: mk_binary_grid(vars, num_cps, k),
        uses_chain: (0..k).map(|_| vars.add(variable().binary())).collect(),
    }
}

fn build_model(vars: ProblemVariables) -> SCIPProblem {
    // Constant objective: any feasible integer solution satisfies the gap
    // limit, so SCIP returns on the first incumbent.
    vars.minimise(0_i32)
        .using(good_lp::solvers::scip::scip)
        .set_option("randomization/randomseedshift", SCIP_RANDOM_SEED)
        .set_verbose(false)
        .set_option("limits/gap", 1e20_f64)
        .set_option("limits/time", SCIP_TIME_LIMIT_SECONDS)
        .set_option("separating/maxrounds", 0_i32)
        .set_option("separating/maxroundsroot", 0_i32)
}

/// Statements reachable from `start` walking backward along Internal
/// dependency edges (i.e. `start` plus its producers, their producers,
/// and so on). Includes `start` itself.
fn reachable_upstream(start: usize, input: &InputShape) -> BTreeSet<usize> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(u) = stack.pop() {
        if !visited.insert(u) {
            continue;
        }
        for dep in &input.dep_edges[u] {
            if let AbstractDep::Internal(d) = dep {
                stack.push(*d);
            }
        }
    }
    visited
}

/// Statements reachable from `start` walking forward along Internal
/// consumer edges. Includes `start` itself. `consumers[d]` is the list of
/// statements that have `Internal(d)` as a dep.
fn reachable_downstream(start: usize, consumers: &[Vec<usize>]) -> BTreeSet<usize> {
    let mut visited: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(u) = stack.pop() {
        if !visited.insert(u) {
            continue;
        }
        for &c in &consumers[u] {
            stack.push(c);
        }
    }
    visited
}

/// Minimum number of PODs needed to hold the given statement subset
/// under the input's per-POD caps. Scoped variant of the resource lower
/// bound used by [`compute_pod_bounds`] for MILP preprocessing.
fn pods_needed_for(stmts: &BTreeSet<usize>, input: &InputShape) -> usize {
    ResourceTotals::accumulate(stmts.iter().map(|&s| &input.costs[s])).min_pods(&input.params)
}

/// Per-statement POD range `[min_pod, max_pod]` derived from resource
/// sums over reachable upstream and downstream sets. Statement `s` and
/// its upstream must fit in PODs `[0, min_pod(s)]`; `s` and its
/// downstream must fit in PODs `[max_pod(s), k-1]`. Outside this range
/// every assignment is structurally infeasible, so we can fix those
/// `assign[s][p]` variables to 0 before SCIP starts. Pure preprocessing:
/// adds no constraints SCIP could later prune as redundant from the LP,
/// and never rules out a feasible partition.
fn compute_pod_bounds(input: &InputShape, k: usize) -> Vec<(usize, usize)> {
    let n = input.num_statements();
    if n == 0 || k == 0 {
        return vec![(0, 0); n];
    }
    let consumers = input.consumers();
    (0..n)
        .map(|s| {
            let upstream = reachable_upstream(s, input);
            let downstream = reachable_downstream(s, &consumers);
            let up_pods = pods_needed_for(&upstream, input);
            let down_pods = pods_needed_for(&downstream, input);
            let min_pod = up_pods.saturating_sub(1);
            let max_pod = (k - 1).saturating_sub(down_pods.saturating_sub(1));
            (min_pod, max_pod)
        })
        .collect()
}

/// Solve the MILP for exactly `k` PODs. Returns `Some(OutputShape)` if a
/// feasible partition exists at this K, `None` otherwise.
pub fn solve_for_k(input: &InputShape, k: usize) -> Option<OutputShape> {
    let n = input.num_statements();
    let num_ext_pods = input.num_external_pods;
    let num_ext_premises = input.num_external_premises();

    // Distinct custom predicate IDs across the problem.
    let mut all_cps: Vec<CustomPredicateId> = input
        .costs
        .iter()
        .flat_map(|c| c.custom_predicates_ids.iter().cloned())
        .collect();
    all_cps.sort();
    all_cps.dedup();
    let num_cps = all_cps.len();

    // Internal-consumer index, deduped so the import-from constraints
    // below don't add the same lower-bound twice when a statement names
    // the same producer in multiple deps.
    let mut consumers = input.consumers();
    for c in &mut consumers {
        c.sort();
        c.dedup();
    }

    // External-pod consumer index: ext_consumers[e] = list of statements
    // with at least one External(e, _) dep.
    let mut ext_consumers: Vec<Vec<usize>> = vec![Vec::new(); num_ext_pods];
    for (s, deps) in input.dep_edges.iter().enumerate() {
        let mut pods_for_s: HashSet<usize> = HashSet::new();
        for dep in deps {
            if let AbstractDep::External { pod, .. } = dep {
                pods_for_s.insert(*pod);
            }
        }
        for e in pods_for_s {
            ext_consumers[e].push(s);
        }
    }

    // External-premise consumer index: ext_premise_consumers[e_prem] = list
    // of statements with at least one External { premise: e_prem, .. } dep.
    let mut ext_premise_consumers: Vec<Vec<usize>> = vec![Vec::new(); num_ext_premises];
    for (s, deps) in input.dep_edges.iter().enumerate() {
        let mut premises_for_s: HashSet<usize> = HashSet::new();
        for dep in deps {
            if let AbstractDep::External { premise, .. } = dep {
                premises_for_s.insert(*premise);
            }
        }
        for e in premises_for_s {
            ext_premise_consumers[e].push(s);
        }
    }

    let output_pub_set: BTreeSet<usize> = input.output_public_indices.iter().copied().collect();
    let last_pod = k - 1;

    let mut vars = ProblemVariables::new();
    let v = declare_vars(&mut vars, n, k, num_ext_pods, num_ext_premises, num_cps);
    let mut model = build_model(vars);

    // (1) Each statement in exactly one POD.
    for s in 0..n {
        let sum: Expression = (0..k).map(|p| v.assign[s][p]).sum();
        model.add_constraint(constraint!(sum == 1));
    }

    // (2) Topological precedence: for each Internal dep (s consumes d), and
    // each POD p, consumer s in p requires producer d in p or earlier.
    for s in 0..n {
        for dep in &input.dep_edges[s] {
            if let AbstractDep::Internal(d) = dep {
                for p in 0..k {
                    let prod_at_or_before: Expression = (0..=p).map(|pp| v.assign[*d][pp]).sum();
                    model.add_constraint(constraint!(v.assign[s][p] <= prod_at_or_before));
                }
            }
        }
    }

    // (3) Statement-table cap per POD. Each `OpenInputStatement` op
    // produces a statement, so the table holds `local statements +
    // chain imports + external-premise imports`, capped by
    // `max_statements`.
    for p in 0..k {
        let assign_sum: Expression = (0..n).map(|s| v.assign[s][p]).sum();
        let chain_sum: Expression = (0..n).map(|d| v.import_from[d][p]).sum();
        let ext_sum: Expression = (0..num_ext_premises)
            .map(|e_prem| v.ext_import_from[e_prem][p])
            .sum();
        model.add_constraint(constraint!(
            assign_sum + chain_sum + ext_sum <= input.params.max_statements as f64
        ));
    }

    // (4) Multi-dim resource caps per POD. Merkle dimensions are
    // absorbable-bin: medium must fit alone, small+medium combined must
    // fit across both pools. Two linear constraints per dimension.
    let state = &input.params.containers.state;
    let transition = &input.params.containers.transition;
    let merkle_proofs_medium_cap = state.max_medium as f64;
    let merkle_proofs_total_cap = state.max_total() as f64;
    let merkle_trans_medium_cap = transition.max_medium as f64;
    let merkle_trans_total_cap = transition.max_total() as f64;
    for p in 0..k {
        let mp_medium: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_proofs_medium as f64) * v.assign[s][p])
            .sum();
        model.add_constraint(constraint!(mp_medium <= merkle_proofs_medium_cap));

        let mp_total: Expression = (0..n)
            .map(|s| {
                ((input.costs[s].merkle_proofs_small + input.costs[s].merkle_proofs_medium) as f64)
                    * v.assign[s][p]
            })
            .sum();
        model.add_constraint(constraint!(mp_total <= merkle_proofs_total_cap));

        let mst_medium: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_state_transitions_medium as f64) * v.assign[s][p])
            .sum();
        model.add_constraint(constraint!(mst_medium <= merkle_trans_medium_cap));

        let mst_total: Expression = (0..n)
            .map(|s| {
                ((input.costs[s].merkle_state_transitions_small
                    + input.costs[s].merkle_state_transitions_medium) as f64)
                    * v.assign[s][p]
            })
            .sum();
        model.add_constraint(constraint!(mst_total <= merkle_trans_total_cap));

        let cpv: Expression = (0..n)
            .map(|s| (input.costs[s].custom_pred_verifications as f64) * v.assign[s][p])
            .sum();
        model.add_constraint(constraint!(
            cpv <= input.params.max_custom_predicate_verifications as f64
        ));

        let sb: Expression = (0..n)
            .map(|s| (input.costs[s].signed_by as f64) * v.assign[s][p])
            .sum();
        model.add_constraint(constraint!(sb <= input.params.max_signed_by as f64));

        let pko: Expression = (0..n)
            .map(|s| (input.costs[s].public_key_of as f64) * v.assign[s][p])
            .sum();
        model.add_constraint(constraint!(pko <= input.params.max_public_key_of as f64));
    }

    // (5) Custom predicate cardinality.
    for (b, cp_id) in all_cps.iter().enumerate() {
        let users: Vec<usize> = (0..n)
            .filter(|&s| input.costs[s].custom_predicates_ids.contains(cp_id))
            .collect();
        for p in 0..k {
            for &s in &users {
                model.add_constraint(constraint!(v.cp_used[b][p] >= v.assign[s][p]));
            }
            let sum: Expression = users.iter().map(|&s| v.assign[s][p]).sum();
            model.add_constraint(constraint!(v.cp_used[b][p] <= sum));
        }
    }
    for p in 0..k {
        let sum: Expression = (0..num_cps).map(|b| v.cp_used[b][p]).sum();
        model.add_constraint(constraint!(
            sum <= input.params.max_custom_predicates as f64
        ));
    }

    // (6) Import definition. For each (d, p):
    //   import_from[d][p] = 1 iff d is needed in p AND d is not in p.
    // "Needed in p" means either (a) some statement in p consumes d via
    // Internal, or (b) p is the output POD and d is output-public.
    for d in 0..n {
        for p in 0..k {
            let is_out_pub_in_last = p == last_pod && output_pub_set.contains(&d);

            // Upper bound: not imported if locally produced.
            model.add_constraint(constraint!(v.import_from[d][p] <= 1 - v.assign[d][p]));

            if is_out_pub_in_last {
                // Forced to (1 - assign[d][p]): output-public is either in
                // the output POD or imported into it.
                model.add_constraint(constraint!(v.import_from[d][p] >= 1 - v.assign[d][p]));
            } else {
                // Upper bound: at most the consumption indicator.
                let sum: Expression = consumers[d].iter().map(|&s| v.assign[s][p]).sum();
                model.add_constraint(constraint!(v.import_from[d][p] <= sum));
                // Lower bound: for each consumer s, force when s is in p
                // and d is not.
                for &s in &consumers[d] {
                    model.add_constraint(constraint!(
                        v.import_from[d][p] >= v.assign[s][p] - v.assign[d][p]
                    ));
                }
            }
        }
    }

    // (7a) External-premise import definition. For each (e_prem, p):
    //   ext_import_from[e_prem][p] = 1 iff some statement in p has an
    //   External { premise: e_prem, .. } dep. External premises are never
    //   "produced locally", so there is no `1 - assign[d][p]` slack term.
    for e_prem in 0..num_ext_premises {
        for p in 0..k {
            let sum: Expression = ext_premise_consumers[e_prem]
                .iter()
                .map(|&s| v.assign[s][p])
                .sum();
            model.add_constraint(constraint!(v.ext_import_from[e_prem][p] <= sum));
            for &s in &ext_premise_consumers[e_prem] {
                model.add_constraint(constraint!(v.ext_import_from[e_prem][p] >= v.assign[s][p]));
            }
        }
    }

    // (7b) Combined import cap: chain + external imports share the
    // `max_open_input_statements` budget (POD circuit reads both kinds
    // through the same input-tree slots).
    let max_imports = input.params.max_open_input_statements as f64;
    for p in 0..k {
        let chain_sum: Expression = (0..n).map(|d| v.import_from[d][p]).sum();
        let ext_sum: Expression = (0..num_ext_premises)
            .map(|e_prem| v.ext_import_from[e_prem][p])
            .sum();
        model.add_constraint(constraint!(chain_sum + ext_sum <= max_imports));
    }

    // (8) External-pod tracking.
    for e in 0..num_ext_pods {
        for p in 0..k {
            for &s in &ext_consumers[e] {
                model.add_constraint(constraint!(v.ext_used[e][p] >= v.assign[s][p]));
            }
            let sum: Expression = ext_consumers[e].iter().map(|&s| v.assign[s][p]).sum();
            model.add_constraint(constraint!(v.ext_used[e][p] <= sum));
        }
    }

    // (9) uses_chain[p] = OR of import_from[*][p].
    for p in 0..k {
        for d in 0..n {
            model.add_constraint(constraint!(v.uses_chain[p] >= v.import_from[d][p]));
        }
        // Upper bound: at most 1 if any import is set. We don't need a
        // tight upper bound since the input-pod cap is the only thing
        // that reads uses_chain, and a slack uses_chain = 1 is harmless
        // when no imports are taken.
        let sum: Expression = (0..n).map(|d| v.import_from[d][p]).sum();
        model.add_constraint(constraint!(v.uses_chain[p] <= sum));
    }

    // (10) Input-pod cap: uses_chain + external pods <= max_input_pods.
    for p in 0..k {
        let ext_sum: Expression = (0..num_ext_pods).map(|e| v.ext_used[e][p]).sum();
        model.add_constraint(constraint!(
            v.uses_chain[p] + ext_sum <= input.params.max_input_pods as f64
        ));
    }

    // (11) POD-range preprocessing: each statement's assignable PODs are
    // bounded by `[min_pod(s), max_pod(s)]` derived from upstream and
    // downstream resource sums. Fix assigns outside this range to 0.
    // Pure constraint tightening; never rules out a feasible partition,
    // but lets SCIP propagate from a smaller LP relaxation.
    let bounds = compute_pod_bounds(input, k);
    for (s, (lo, hi)) in bounds.iter().enumerate() {
        for p in 0..k {
            if p < *lo || p > *hi {
                model.add_constraint(constraint!(v.assign[s][p] == 0));
            }
        }
    }

    let solution = model.solve().ok()?;

    let mut pod_statements: Vec<Vec<usize>> = vec![Vec::new(); k];
    for s in 0..n {
        for p in 0..k {
            if solution.value(v.assign[s][p]) > SOLVER_BINARY_THRESHOLD {
                pod_statements[p].push(s);
                break;
            }
        }
    }
    for stmts in &mut pod_statements {
        stmts.sort();
    }

    Some(OutputShape {
        pod_count: k,
        pod_statements,
        pod_republished_externals: vec![BTreeSet::new(); k],
    })
}

/// Find a feasible partition by trying K = 1, 2, ..., n.
pub(super) fn solve(input: &InputShape) -> Option<OutputShape> {
    let n = input.num_statements();
    if n == 0 {
        return Some(OutputShape {
            pod_count: 0,
            pod_statements: vec![],
            pod_republished_externals: vec![],
        });
    }
    for k in 1..=n {
        if let Some(out) = solve_for_k(input, k) {
            return Some(out);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        frontend::multi_pod_tree::{cost::StatementCost, partition},
        middleware::Params,
    };

    fn independent(n: usize, output_public: Vec<usize>, params: Params) -> InputShape {
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
    fn single_pod_when_caps_allow() {
        let input = independent(3, vec![0, 1, 2], Params::default());
        let out = solve(&input).expect("MILP should find a feasible partition");
        assert_eq!(out.pod_count, 1);
        assert_eq!(out.pod_statements[0], vec![0, 1, 2]);
    }

    #[test]
    fn external_imports_count_against_max_open_input_statements() {
        // n statements with one External dep each, all referencing the
        // same external pod with distinct premises. K=1 must be infeasible
        // because the combined import cap (chain + external) is busted.
        let params = Params::default();
        let n = params.max_open_input_statements + 1;
        let input = InputShape {
            costs: (0..n).map(|_| StatementCost::default()).collect(),
            dep_edges: (0..n)
                .map(|i| vec![AbstractDep::External { pod: 0, premise: i }])
                .collect(),
            output_public_indices: vec![0],
            num_external_pods: 1,
            premise_pod: vec![0; n],
            params,
        };
        assert!(
            solve_for_k(&input, 1).is_none(),
            "MILP must reject K=1 when external imports exceed max_open_input_statements"
        );
        assert!(
            solve_for_k(&input, 2).is_some(),
            "MILP must accept K=2 for the same input"
        );
    }

    #[test]
    fn splits_into_two_pods_when_count_exceeds_cap() {
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        // max_statements = 2, so 3 statements must split.
        let input = independent(3, vec![2], params);
        let out = solve(&input).expect("MILP should find a feasible partition");
        assert_eq!(out.pod_count, 2);
        let mut all: Vec<usize> = out.pod_statements.iter().flatten().copied().collect();
        all.sort();
        assert_eq!(all, vec![0, 1, 2]);
    }

    /// Random `InputShape` generator. Covers internal dep graphs (up to 2
    /// deps per statement), occasional external deps (drawn from 0-2
    /// external pods with up to 3 premises each), and per-statement
    /// resource costs (signed_by / merkle_proofs).
    fn random_input(rng: &mut rand_chacha::ChaCha20Rng, n: usize, params: Params) -> InputShape {
        use rand::{seq::SliceRandom, Rng};

        let num_external_pods = rng.gen_range(0..=2);
        let num_premises = if num_external_pods > 0 {
            rng.gen_range(0..=(num_external_pods * 3))
        } else {
            0
        };
        let premise_pod: Vec<usize> = (0..num_premises)
            .map(|_| rng.gen_range(0..num_external_pods))
            .collect();

        let dep_edges: Vec<Vec<AbstractDep>> = (0..n)
            .map(|i| {
                let mut deps: Vec<AbstractDep> = Vec::new();
                let max_internal = i.min(3);
                if max_internal > 0 {
                    let num = rng.gen_range(0..=max_internal);
                    let mut taken: HashSet<usize> = HashSet::new();
                    let mut attempts = 0;
                    while deps.len() < num && attempts < 10 {
                        attempts += 1;
                        let j = rng.gen_range(0..i);
                        if taken.insert(j) {
                            deps.push(AbstractDep::Internal(j));
                        }
                    }
                }
                if num_premises > 0 && rng.gen_bool(0.5) {
                    let premise = rng.gen_range(0..num_premises);
                    deps.push(AbstractDep::External {
                        pod: premise_pod[premise],
                        premise,
                    });
                }
                deps
            })
            .collect();

        let costs: Vec<StatementCost> = (0..n)
            .map(|_| {
                let mut c = StatementCost::default();
                if rng.gen_bool(0.15) {
                    c.signed_by = 1;
                }
                if rng.gen_bool(0.15) {
                    // Random test fixture: charge to the medium slot so the
                    // generated cost is feasible regardless of caps tuning.
                    c.merkle_proofs_medium = 1;
                }
                c
            })
            .collect();

        let n_pub = rng.gen_range(1..=2.min(n));
        let mut indices: Vec<usize> = (0..n).collect();
        indices.shuffle(rng);
        indices.truncate(n_pub);
        indices.sort();

        InputShape {
            costs,
            dep_edges,
            output_public_indices: indices,
            num_external_pods,
            premise_pod,
            params,
        }
    }

    /// Randomised DP-vs-MILP parity sweep.
    ///
    /// For each generated input, measures K from two sources:
    /// - `K_full`: the production heuristic pipeline (`partition`).
    /// - `K_milp`: MILP optimum.
    ///
    /// Asserts feasibility parity (DP must succeed wherever MILP does)
    /// and reports counts of `optimality_gaps` (`K_full > K_milp`).
    ///
    /// `#[ignore]`d because each trial invokes SCIP. Run with
    /// `cargo test --release dp_milp_parity -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn dp_milp_parity() {
        use std::time::{Duration, Instant};

        use rand::SeedableRng;
        use rand_chacha::ChaCha20Rng;

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
        // Mixed sizes: small to keep MILP cheap, mid-size to give the
        // heuristic room to make the kind of mistakes refinement could
        // surface.
        let n_values: Vec<usize> = vec![8, 12, 16, 24, 32];
        let trials_per_combo: usize = 25;

        let mut rng = ChaCha20Rng::seed_from_u64(0xDEADBEEF);
        let mut checked = 0_usize;
        let mut milp_feasible = 0_usize;
        let mut feasibility_divergences = 0_usize;
        let mut optimality_divergences = 0_usize;
        let mut total_k_gap = 0_usize;
        let mut max_k_gap = 0_usize;
        let mut milp_total_time = Duration::ZERO;
        let mut milp_max_time = Duration::ZERO;

        for (label, params) in &param_variants {
            for &n in &n_values {
                for trial in 0..trials_per_combo {
                    let input = random_input(&mut rng, n, params.clone());

                    let milp_start = Instant::now();
                    let milp_out = solve(&input);
                    let elapsed = milp_start.elapsed();
                    milp_total_time += elapsed;
                    if elapsed > milp_max_time {
                        milp_max_time = elapsed;
                    }
                    let dp_out = partition::partition(&input);

                    checked += 1;
                    let Some(milp_sol) = milp_out else { continue };
                    milp_feasible += 1;
                    match &dp_out {
                        None => {
                            feasibility_divergences += 1;
                            eprintln!(
                                "FEASIBILITY DIVERGENCE [{} n={} trial={}]: MILP={} PODs, DP=none",
                                label, n, trial, milp_sol.pod_count
                            );
                        }
                        Some(dp_sol) if dp_sol.pod_count > milp_sol.pod_count => {
                            optimality_divergences += 1;
                            let gap = dp_sol.pod_count - milp_sol.pod_count;
                            total_k_gap += gap;
                            if gap > max_k_gap {
                                max_k_gap = gap;
                            }
                            eprintln!(
                                "OPTIMALITY GAP [{} n={} trial={}]: MILP={} PODs, DP={} PODs",
                                label, n, trial, milp_sol.pod_count, dp_sol.pod_count
                            );
                        }
                        Some(_) => {}
                    }
                }
            }
        }

        eprintln!();
        eprintln!("=== DP-vs-MILP parity sweep ===");
        eprintln!(
            "  checked={} milp_feasible={} feasibility_divergences={} optimality_gaps={}",
            checked, milp_feasible, feasibility_divergences, optimality_divergences
        );
        if optimality_divergences > 0 {
            eprintln!(
                "  optimality gap stats: total={} max_per_input={} mean={:.2}",
                total_k_gap,
                max_k_gap,
                total_k_gap as f64 / optimality_divergences as f64
            );
        }
        let safe_mean = if checked == 0 {
            Duration::ZERO
        } else {
            milp_total_time / checked as u32
        };
        eprintln!(
            "  MILP timing: total={:?} mean={:?} max={:?}",
            milp_total_time, safe_mean, milp_max_time
        );

        assert_eq!(
            feasibility_divergences, 0,
            "DP failed where MILP succeeded on {} inputs",
            feasibility_divergences
        );
    }
}
