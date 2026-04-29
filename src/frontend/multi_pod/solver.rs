//! MILP solver for multi-POD packing.
//!
//! This module builds and solves a Mixed Integer Linear Program (MILP) to minimize
//! the number of PODs needed to prove a set of statements while respecting resource
//! limits and dependency constraints.
//!
//! The solver is purely symbolic: it consumes an [`InputShape`] (positional
//! dependency graph plus resource costs and params) and produces an
//! [`OutputShape`] (positional POD assignments). It never sees concrete pod
//! hashes or statement values; the calling layer reattaches those after the
//! solve via its own side table.
//!
//! # Constraint Overview
//!
//! The solver uses the following constraints (numbered for reference in code comments):
//!
//! - **Constraint 1 (Coverage)**: Each statement must be proved in at least one POD.
//! - **Constraint 2 (Output POD)**: Output-public statements must be public in the last POD.
//! - **Constraint 2b (Privacy)**: Non-output-public statements cannot be public in the output POD.
//! - **Constraint 3 (Public ⇒ Proved)**: A statement can only be public if it's proved there.
//! - **Constraint 4 (POD Existence)**: If any statement is proved in POD p, then p is used.
//! - **Constraint 5 (Dependencies)**: If statement S depends on D and S is proved in POD p,
//!   then D must be available: either proved locally in p, or public in some earlier POD.
//! - **Constraint 6 (Resource Limits)**: Per-POD limits on statements, public slots, merkle
//!   proofs, custom predicates, batches, etc.
//! - **Constraint 7 (Batch Cardinality)**: Limit distinct custom predicate batches per POD.
//! - **Constraint 7b (Anchored Keys)**: Track auto-inserted Contains for anchored key references.
//! - **Constraint 8a (Internal Inputs)**: Track which earlier PODs are used as inputs.
//! - **Constraint 8b (External Dep Inputs)**: Track when external dependencies are sourced from
//!   earlier PODs instead of direct external inputs.
//! - **Constraint 8c (External Forward Inputs)**: Track inputs required when forwarding external
//!   premises publicly across PODs.
//! - **Constraint 8d (Input Limit)**: Total inputs (internal + external) <= max_input_pods.
//! - **Constraint 9 (Symmetry Breaking)**: PODs are used in order (0, 1, 2, ...) with no gaps.
//! - **Constraint 10 (External Public Availability)**: External premises can be made public only
//!   when available in that POD.
//!
//! # Solution Approach
//!
//! The solver uses an incremental approach: it tries solving with the minimum possible
//! number of PODs first, then increments until a feasible solution is found. This is
//! efficient for the common case where few PODs are needed.

// MILP constraint building uses explicit index loops for clarity
#![allow(clippy::needless_range_loop)]

use std::{collections::BTreeSet, time::Instant};

use good_lp::{
    constraint, default_solver, variable, Expression, ProblemVariables, ResolutionError, Solution,
    SolverModel, Variable,
};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use super::{cost::CustomPredicateId, Result};
use crate::{frontend::multi_pod::cost::StatementCost, middleware::Params};

/// Threshold for interpreting MILP solver's floating-point results as binary.
/// The solver returns continuous values in [0, 1] for binary variables;
/// values > 0.5 are interpreted as "true" (1), otherwise "false" (0).
const SOLVER_BINARY_THRESHOLD: f64 = 0.5;

/// Positional dependency. Indices keep the solver input/output cache-stable
/// across builders that differ only in concrete pod hashes or statement
/// values.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AbstractDep {
    Internal(usize),
    External { pod: usize, premise: usize },
}

/// Symbolic input to the solver: the structure of a multi-POD problem with
/// no concrete pod hashes or statement values.
///
/// Two builders that produce equal `InputShape`s will produce equal
/// `OutputShape`s, so this type doubles as the cache key for solver results.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct InputShape {
    pub costs: Vec<StatementCost>,
    /// Adjacency in positional form: `dep_edges[s]` are the deps of statement `s`.
    pub dep_edges: Vec<Vec<AbstractDep>>,
    pub output_public_indices: Vec<usize>,
    pub params: Params,
    pub num_external_pods: usize,
    /// `premise_pod[u]` is the source pod index (in `0..num_external_pods`)
    /// of premise `u`. Length equals the number of external premises.
    pub premise_pod: Vec<usize>,
    /// Search bound used at solve time. Part of the cache key so a layout
    /// solved at a larger `max_pods` isn't reused at a tighter bound that
    /// the cached `pod_count` might exceed, and so cached infeasibility is
    /// only authoritative at the `max_pods` it was solved against.
    pub max_pods: usize,
}

impl InputShape {
    pub fn num_statements(&self) -> usize {
        self.costs.len()
    }

    pub fn num_external_premises(&self) -> usize {
        self.premise_pod.len()
    }
}

/// Symbolic output of the solver: positional POD assignments. Concrete
/// external pod hashes and premise statements are reattached by the build
/// layer via its own side table.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct OutputShape {
    pub pod_count: usize,
    /// A statement may appear in multiple PODs when re-proving is cheaper
    /// than copying.
    pub statement_to_pods: Vec<Vec<usize>>,
    pub pod_statements: Vec<Vec<usize>>,
    pub pod_public_statements: Vec<BTreeSet<usize>>,
    pub pod_internal_inputs: Vec<BTreeSet<usize>>,
    pub pod_external_inputs: Vec<BTreeSet<usize>>,
    pub pod_public_external_premises: Vec<BTreeSet<usize>>,
}

#[derive(Clone, Copy, Debug, Default)]
struct ResourceTotals {
    merkle_proofs: usize,
    merkle_state_transitions: usize,
    custom_pred_verifications: usize,
    signed_by: usize,
    public_key_of: usize,
}

impl ResourceTotals {
    fn from_costs(costs: &[StatementCost]) -> Self {
        costs.iter().fold(Self::default(), |mut totals, c| {
            totals.merkle_proofs += c.merkle_proofs;
            totals.merkle_state_transitions += c.merkle_state_transitions;
            totals.custom_pred_verifications += c.custom_pred_verifications;
            totals.signed_by += c.signed_by;
            totals.public_key_of += c.public_key_of;
            totals
        })
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct DependencyStats {
    internal_edges: usize,
    external_edges: usize,
}

#[derive(Clone, Copy, Debug)]
struct SolveDebugContext {
    dep_stats: DependencyStats,
    batch_memberships: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct ModelSizeEstimate {
    vars_prove: usize,
    vars_public: usize,
    vars_public_external: usize,
    vars_pod_used: usize,
    vars_batch_used: usize,
    vars_uses_input: usize,
    vars_uses_external: usize,
    vars_total: usize,
    c1_coverage: usize,
    c2_output_public: usize,
    c2b_output_privacy: usize,
    c3_public_implies_proved: usize,
    c4_pod_existence: usize,
    c5_internal_dependencies: usize,
    c5_external_dependencies: usize,
    c6_pre_content_group: usize,
    c6_resource_limits: usize,
    c7_batch_cardinality: usize,
    c8a_internal_inputs: usize,
    c8b_external_dep_inputs: usize,
    c8c_external_forward_inputs: usize,
    c8d_input_limit: usize,
    c10_external_public_availability: usize,
    c10b_external_public_implies_pod_used: usize,
    c9_symmetry_breaking: usize,
    constraints_total: usize,
}

impl ModelSizeEstimate {
    fn for_target_pods(
        shape: &InputShape,
        target_pods: usize,
        all_batches_len: usize,
        debug_ctx: &SolveDebugContext,
    ) -> Self {
        let n = shape.num_statements();
        let external_pods_len = shape.num_external_pods;
        let external_premises_len = shape.num_external_premises();
        let triangular_k = target_pods * target_pods.saturating_sub(1) / 2;

        let vars_prove = n * target_pods;
        let vars_public = n * target_pods;
        let vars_public_external = external_premises_len * target_pods;
        let vars_pod_used = target_pods;
        let vars_batch_used = all_batches_len * target_pods;
        let vars_uses_input = triangular_k;
        let vars_uses_external = external_pods_len * target_pods;
        let vars_total = vars_prove
            + vars_public
            + vars_public_external
            + vars_pod_used
            + vars_batch_used
            + vars_uses_input
            + vars_uses_external;

        let c1_coverage = n;
        let c2_output_public = shape.output_public_indices.len();
        let c2b_output_privacy = n.saturating_sub(c2_output_public);
        let c3_public_implies_proved = n * target_pods;
        let c4_pod_existence = n * target_pods;
        let c5_internal_dependencies = debug_ctx.dep_stats.internal_edges * target_pods;
        let c5_external_dependencies = debug_ctx.dep_stats.external_edges * target_pods;
        let c6_pre_content_group = n * target_pods;
        let c6_resource_limits = 7 * target_pods;
        let c7_batch_cardinality =
            (debug_ctx.batch_memberships * target_pods) + (all_batches_len * target_pods);
        let c8a_internal_inputs = debug_ctx.dep_stats.internal_edges * triangular_k;
        let c8b_external_dep_inputs = debug_ctx.dep_stats.external_edges * triangular_k;
        let c8c_external_forward_inputs = external_premises_len * triangular_k;
        let c8d_input_limit = target_pods;
        let c10_external_public_availability = external_premises_len * target_pods;
        let c10b_external_public_implies_pod_used = external_premises_len * target_pods;
        let c9_symmetry_breaking = target_pods.saturating_sub(1);
        let constraints_total = c1_coverage
            + c2_output_public
            + c2b_output_privacy
            + c3_public_implies_proved
            + c4_pod_existence
            + c5_internal_dependencies
            + c5_external_dependencies
            + c6_pre_content_group
            + c6_resource_limits
            + c7_batch_cardinality
            + c8a_internal_inputs
            + c8b_external_dep_inputs
            + c8c_external_forward_inputs
            + c8d_input_limit
            + c10_external_public_availability
            + c10b_external_public_implies_pod_used
            + c9_symmetry_breaking;

        Self {
            vars_prove,
            vars_public,
            vars_public_external,
            vars_pod_used,
            vars_batch_used,
            vars_uses_input,
            vars_uses_external,
            vars_total,
            c1_coverage,
            c2_output_public,
            c2b_output_privacy,
            c3_public_implies_proved,
            c4_pod_existence,
            c5_internal_dependencies,
            c5_external_dependencies,
            c6_pre_content_group,
            c6_resource_limits,
            c7_batch_cardinality,
            c8a_internal_inputs,
            c8b_external_dep_inputs,
            c8c_external_forward_inputs,
            c8d_input_limit,
            c10_external_public_availability,
            c10b_external_public_implies_pod_used,
            c9_symmetry_breaking,
            constraints_total,
        }
    }
}

fn dependency_stats(dep_edges: &[Vec<AbstractDep>]) -> DependencyStats {
    let mut stats = DependencyStats::default();
    for edges in dep_edges {
        for dep in edges {
            match dep {
                AbstractDep::Internal(_) => stats.internal_edges += 1,
                AbstractDep::External { .. } => stats.external_edges += 1,
            }
        }
    }
    stats
}

fn lower_bound_from_total(total: usize, per_pod_limit: usize) -> Option<usize> {
    if total == 0 {
        Some(0)
    } else if per_pod_limit == 0 {
        None
    } else {
        Some(total.div_ceil(per_pod_limit))
    }
}

fn format_lower_bound(lb: Option<usize>) -> String {
    lb.map_or_else(|| "inf".to_string(), |v| v.to_string())
}

/// Solve wrapped for the cache layer: returns the solver's error message as
/// `Err` instead of an [`Error`], so cache::get can persist infeasibility too.
/// `solve_cached` propagates cached errors instead of repeatedly hammering
/// the solver.
pub fn solve_for_cache(shape: &InputShape) -> std::result::Result<OutputShape, String> {
    solve(shape).map_err(|e| e.to_string())
}

/// Solve the MILP problem to find optimal POD packing.
///
/// Uses an incremental approach: tries solving with min_pods first,
/// then increments until a solution is found or target_pods is exceeded.
/// This is efficient for the common case where min_pods is sufficient.
pub fn solve(shape: &InputShape) -> Result<OutputShape> {
    let n = shape.num_statements();

    // Require at least one public statement. A POD with no public statements
    // can't prove anything to an external verifier.
    if shape.output_public_indices.is_empty() {
        return Err(super::Error::Solver(
            "No public statements requested. Use pub_op() to add at least one statement \
             that should be visible in the output POD."
                .to_string(),
        ));
    }

    // Check that all output-public statements can fit in a single POD
    let num_output_public = shape.output_public_indices.len();
    if num_output_public > shape.params.max_public_statements {
        return Err(super::Error::Solver(format!(
            "Too many public statements requested: {} requested, but max_public_statements is {}. \
             All public statements must fit in a single output POD.",
            num_output_public, shape.params.max_public_statements
        )));
    }

    // Lower bound on number of PODs needed
    // Note: max_priv_statements is the limit on total unique statements per POD
    // (public statements are copies from private slots)
    let max_stmts_per_pod = shape.params.max_priv_statements();
    let min_pods_by_statements = n.div_ceil(max_stmts_per_pod);
    let min_pods = min_pods_by_statements.max(1);

    // Check if the problem exceeds the configured max_pods limit
    if min_pods > shape.max_pods {
        return Err(super::Error::Solver(format!(
            "Problem requires at least {} PODs, but max_pods is set to {}. \
             Increase Options::max_pods to allow more PODs.",
            min_pods, shape.max_pods
        )));
    }

    // Collect all unique custom predicate IDs used
    let all_custom_predicates: Vec<CustomPredicateId> = shape
        .costs
        .iter()
        .flat_map(|c| c.custom_predicates_ids.iter().cloned())
        .unique()
        .collect();

    let dep_stats = dependency_stats(&shape.dep_edges);
    let batch_memberships: usize = shape
        .costs
        .iter()
        .map(|c| c.custom_predicates_ids.len())
        .sum();
    let debug_ctx = SolveDebugContext {
        dep_stats,
        batch_memberships,
    };

    if log::log_enabled!(log::Level::Debug) {
        let resource_totals = ResourceTotals::from_costs(&shape.costs);
        let lb_statement_groups = lower_bound_from_total(n, max_stmts_per_pod);
        let lb_merkle = lower_bound_from_total(
            resource_totals.merkle_proofs,
            shape.params.max_merkle_proofs_containers,
        );
        let lb_merkle_transitions = lower_bound_from_total(
            resource_totals.merkle_state_transitions,
            shape
                .params
                .max_merkle_tree_state_transition_proofs_containers,
        );
        let lb_custom_pred_verifications = lower_bound_from_total(
            resource_totals.custom_pred_verifications,
            shape.params.max_custom_predicate_verifications,
        );
        let lb_signed_by =
            lower_bound_from_total(resource_totals.signed_by, shape.params.max_signed_by);
        let lb_public_key_of = lower_bound_from_total(
            resource_totals.public_key_of,
            shape.params.max_public_key_of,
        );
        let lower_bound_candidates = [
            ("statements_raw", Some(min_pods_by_statements)),
            ("merkle_proofs", lb_merkle),
            ("merkle_state_transitions", lb_merkle_transitions),
            ("custom_pred_verifications", lb_custom_pred_verifications),
            ("signed_by", lb_signed_by),
            ("public_key_of", lb_public_key_of),
        ];
        let dominant_lb = lower_bound_candidates
            .iter()
            .max_by_key(|(_, lb)| lb.unwrap_or(usize::MAX))
            .expect("non-empty lower-bound candidate list");

        log::debug!(
            "MILP summary: statements={} output_public={} \
             custom_predicates={} deps_internal_edges={} deps_external_edges={} external_input_pods={} \
             external_premises={} search_min_pods={} max_pods={}",
            n,
            num_output_public,
            all_custom_predicates.len(),
            dep_stats.internal_edges,
            dep_stats.external_edges,
            shape.num_external_pods,
            shape.num_external_premises(),
            min_pods,
            shape.max_pods
        );
        log::debug!(
            "MILP resource totals: merkle_proofs={} merkle_state_transitions={} \
             custom_pred_verifications={} signed_by={} public_key_of={} \
             batch_memberships={}",
            resource_totals.merkle_proofs,
            resource_totals.merkle_state_transitions,
            resource_totals.custom_pred_verifications,
            resource_totals.signed_by,
            resource_totals.public_key_of,
            batch_memberships,
        );
        log::debug!(
            "MILP lower bounds (pods): statements_raw={} statements_dedup={} merkle_proofs={} \
             merkle_state_transitions={} custom_pred_verifications={} signed_by={} \
             public_key_of={} dominant={}({})",
            min_pods_by_statements,
            format_lower_bound(lb_statement_groups),
            format_lower_bound(lb_merkle),
            format_lower_bound(lb_merkle_transitions),
            format_lower_bound(lb_custom_pred_verifications),
            format_lower_bound(lb_signed_by),
            format_lower_bound(lb_public_key_of),
            dominant_lb.0,
            format_lower_bound(dominant_lb.1)
        );
    }

    // Incremental approach: try solving with increasing POD counts
    // Start with min_pods and increment until we find a feasible solution
    for target_pods in min_pods..=shape.max_pods {
        log::debug!("Trying to solve with {} PODs", target_pods);
        if let Some(solution) =
            try_solve_with_pods(shape, target_pods, &all_custom_predicates, &debug_ctx)?
        {
            return Ok(solution);
        }
        // Infeasible with target_pods, try more
    }

    // No feasible solution found even with max_pods
    Err(super::Error::Solver(format!(
        "No feasible solution found with up to {} PODs",
        shape.max_pods
    )))
}

/// Try to solve the packing problem with exactly `target_pods` PODs.
///
/// Builds a MILP model with all constraints and attempts to solve it.
/// Returns `Ok(Some(solution))` if a feasible assignment exists,
/// `Ok(None)` if the problem is infeasible with this many PODs.
///
/// The caller (in `solve()`) handles incrementing `target_pods` when infeasible.
fn try_solve_with_pods(
    shape: &InputShape,
    target_pods: usize,
    all_custom_predicates: &[CustomPredicateId],
    debug_ctx: &SolveDebugContext,
) -> Result<Option<OutputShape>> {
    let attempt_started_at = Instant::now();

    let n = shape.num_statements();
    let num_external_pods = shape.num_external_pods;
    let num_external_premises = shape.num_external_premises();

    // Create variables
    let mut vars = ProblemVariables::new();

    // prove[s][p] - statement s is proved in POD p
    let prove: Vec<Vec<Variable>> = (0..n)
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // public[s][p] - statement s is public in POD p
    let public: Vec<Vec<Variable>> = (0..n)
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // pod_used[p] - POD p is used
    let pod_used: Vec<Variable> = (0..target_pods)
        .map(|_| vars.add(variable().binary()))
        .collect();

    // custom_predicates[b][p] - custom predicate b is used in POD p
    let custom_predicate_used: Vec<Vec<Variable>> = (0..all_custom_predicates.len())
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // uses_input[p][pp] - POD p uses POD pp as an input (pp < p)
    // We only create variables for pp < p
    let uses_input: Vec<Vec<Variable>> = (0..target_pods)
        .map(|p| (0..p).map(|_| vars.add(variable().binary())).collect())
        .collect();

    // uses_external[p][e] - POD p uses external POD e as an input
    let uses_external: Vec<Vec<Variable>> = (0..target_pods)
        .map(|_| {
            (0..num_external_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // public_external[u][p] - external premise u is exposed publicly in POD p
    let public_external: Vec<Vec<Variable>> = (0..num_external_premises)
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    if log::log_enabled!(log::Level::Debug) {
        let estimate = ModelSizeEstimate::for_target_pods(
            shape,
            target_pods,
            all_custom_predicates.len(),
            debug_ctx,
        );
        log::debug!(
            "MILP(k={}) model estimate vars_total={} [prove={} public={} pod_used={} \
             public_external={} batch_used={} uses_input={} \
             uses_external={}]",
            target_pods,
            estimate.vars_total,
            estimate.vars_prove,
            estimate.vars_public,
            estimate.vars_pod_used,
            estimate.vars_public_external,
            estimate.vars_batch_used,
            estimate.vars_uses_input,
            estimate.vars_uses_external,
        );
        log::debug!(
            "MILP(k={}) model estimate constraints_total={} [c1={} c2={} c2b={} c3={} c4={} \
             c5i={} c5e={} c6_pre={} c6_limits={} c7={} c8a={} c8b={} c8c={} \
             c8d={} c9={} c10={} c10b={}]",
            target_pods,
            estimate.constraints_total,
            estimate.c1_coverage,
            estimate.c2_output_public,
            estimate.c2b_output_privacy,
            estimate.c3_public_implies_proved,
            estimate.c4_pod_existence,
            estimate.c5_internal_dependencies,
            estimate.c5_external_dependencies,
            estimate.c6_pre_content_group,
            estimate.c6_resource_limits,
            estimate.c7_batch_cardinality,
            estimate.c8a_internal_inputs,
            estimate.c8b_external_dep_inputs,
            estimate.c8c_external_forward_inputs,
            estimate.c8d_input_limit,
            estimate.c9_symmetry_breaking,
            estimate.c10_external_public_availability,
            estimate.c10b_external_public_implies_pod_used
        );
    }

    // No optimization objective needed - we use an incremental approach that tries
    // min_pods first and increments until feasible. Combined with symmetry breaking
    // (Constraint 9), this finds the minimum number of PODs without needing MILP
    // optimization. A constant objective makes the solver find any feasible solution.
    let mut model = vars.minimise(0_i32).using(default_solver);

    // Constraint 1: Each statement must be proved at least once
    for s in 0..n {
        let sum: Expression = prove[s].iter().sum();
        model.add_constraint(constraint!(sum >= 1));
    }

    // Constraint 2: Output-public statements must be public in the output POD (last POD)
    // The output POD is at index target_pods-1, allowing it to access all earlier PODs
    // for dependencies. This ensures exactly one output POD with deterministic location.
    let output_pod = target_pods - 1;
    for &s in &shape.output_public_indices {
        model.add_constraint(constraint!(public[s][output_pod] == 1));
    }

    // Constraint 2b: Non-output-public statements cannot be public in the output POD
    // This prevents private statements from leaking to the output POD's public slots.
    for s in 0..n {
        if !shape.output_public_indices.contains(&s) {
            model.add_constraint(constraint!(public[s][output_pod] == 0));
        }
    }

    // Constraint 3: Public implies proved
    for s in 0..n {
        for p in 0..target_pods {
            model.add_constraint(constraint!(public[s][p] <= prove[s][p]));
        }
    }

    // Constraint 4: Pod existence - if any statement is proved in p, p is used
    for s in 0..n {
        for p in 0..target_pods {
            model.add_constraint(constraint!(prove[s][p] <= pod_used[p]));
        }
    }

    // Constraint 5: Dependency availability.
    //
    // Internal dependency (s depends on d):
    //   prove[s][p] <= prove[d][p] + sum_{pp < p} public[d][pp]
    //
    // External dependency (s depends on external premise u from external POD e):
    //   prove[s][p] <= uses_external[p][e] + sum_{pp < p} public_external[u][pp]
    //
    // This captures the intended non-sticky semantics for external premises:
    // a consumer POD can use the external POD directly, OR consume an earlier POD
    // that made the external premise public.
    for s in 0..n {
        for dep in &shape.dep_edges[s] {
            match dep {
                AbstractDep::Internal(d) => {
                    for p in 0..target_pods {
                        let mut rhs: Expression = prove[*d][p].into();
                        for pp in 0..p {
                            rhs += public[*d][pp];
                        }
                        model.add_constraint(constraint!(prove[s][p] <= rhs));
                    }
                }
                AbstractDep::External { pod: e, premise: u } => {
                    for p in 0..target_pods {
                        let mut rhs: Expression = uses_external[p][*e].into();
                        for pp in 0..p {
                            rhs += public_external[*u][pp];
                        }
                        model.add_constraint(constraint!(prove[s][p] <= rhs));
                    }
                }
            }
        }
    }

    // Constraint 10: External-public availability and pod usage.
    //
    // An external premise can be made public in POD p iff it is available there:
    // either directly from its source external input POD, or from an earlier POD
    // that already exposed it publicly.
    for u in 0..num_external_premises {
        let e = shape.premise_pod[u];
        for p in 0..target_pods {
            let mut rhs: Expression = uses_external[p][e].into();
            for pp in 0..p {
                rhs += public_external[u][pp];
            }
            model.add_constraint(constraint!(public_external[u][p] <= rhs));
            model.add_constraint(constraint!(public_external[u][p] <= pod_used[p]));
        }
    }

    for p in 0..target_pods {
        // 6a: Statement count
        let stmt_sum: Expression = (0..n).map(|g| prove[g][p]).sum();
        model.add_constraint(constraint!(
            stmt_sum <= (shape.params.max_priv_statements() as f64) * pod_used[p]
        ));

        // 6b: Public statement count (internal public statements + forwarded external premises)
        let pub_sum_internal: Expression = (0..n).map(|s| public[s][p]).sum();
        let pub_sum_external: Expression = (0..num_external_premises)
            .map(|u| public_external[u][p])
            .sum();
        model.add_constraint(constraint!(
            pub_sum_internal + pub_sum_external
                <= (shape.params.max_public_statements as f64) * pod_used[p]
        ));

        // 6c: Merkle proofs
        let merkle_sum: Expression = (0..n)
            .map(|s| (shape.costs[s].merkle_proofs as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            merkle_sum <= (shape.params.max_merkle_proofs_containers as f64) * pod_used[p]
        ));

        // 6d: Merkle state transitions
        let mst_sum: Expression = (0..n)
            .map(|s| (shape.costs[s].merkle_state_transitions as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            mst_sum
                <= (shape
                    .params
                    .max_merkle_tree_state_transition_proofs_containers as f64)
                    * pod_used[p]
        ));

        // 6e: Custom predicate verifications
        let cpv_sum: Expression = (0..n)
            .map(|s| (shape.costs[s].custom_pred_verifications as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            cpv_sum <= (shape.params.max_custom_predicate_verifications as f64) * pod_used[p]
        ));

        // 6f: SignedBy
        let sb_sum: Expression = (0..n)
            .map(|s| (shape.costs[s].signed_by as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            sb_sum <= (shape.params.max_signed_by as f64) * pod_used[p]
        ));

        // 6g: PublicKeyOf
        let pko_sum: Expression = (0..n)
            .map(|s| (shape.costs[s].public_key_of as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            pko_sum <= (shape.params.max_public_key_of as f64) * pod_used[p]
        ));
    }

    // Constraint 7: Batch cardinality
    // custom_predicate_used[b][p] >= prove[s][p] for all s that use custom predicate b (custom
    // predicate is used if any statement uses it)
    // custom_predicate_used[b][p] <= sum of prove[s][p] for all s using custom predicate b (custom
    // predicate is 0 if no statements use it)
    for (b, predicate_id) in all_custom_predicates.iter().enumerate() {
        for p in 0..target_pods {
            let mut sum: Expression = 0.into();
            for s in 0..n {
                if shape.costs[s].custom_predicates_ids.contains(predicate_id) {
                    model.add_constraint(constraint!(custom_predicate_used[b][p] >= prove[s][p]));
                    sum += prove[s][p];
                }
            }
            model.add_constraint(constraint!(custom_predicate_used[b][p] <= sum));
        }
    }

    // Custom predicate count per POD
    for p in 0..target_pods {
        let custom_predicate_sum: Expression = (0..all_custom_predicates.len())
            .map(|b| custom_predicate_used[b][p])
            .sum();
        model.add_constraint(constraint!(
            custom_predicate_sum <= (shape.params.max_custom_predicates as f64) * pod_used[p]
        ));
    }

    // Constraint 8a: Internal input POD tracking using uses_input.
    // If s is proved in p and depends on internal d exposed by pp, then pp must be counted
    // as an input unless d is also proved locally in p.
    for s in 0..n {
        for dep in &shape.dep_edges[s] {
            if let AbstractDep::Internal(d) = dep {
                for p in 1..target_pods {
                    for pp in 0..p {
                        model.add_constraint(constraint!(
                            uses_input[p][pp] >= prove[s][p] + public[*d][pp] - prove[*d][p] - 1.0
                        ));
                    }
                }
            }
        }
    }

    // Constraint 8b: External dependency input tracking via earlier PODs.
    // If s is proved in p, and external premise u is provided by earlier POD pp
    // (i.e., public_external[u][pp] = 1), then pp must be counted as an input unless
    // p uses the source external POD directly.
    for s in 0..n {
        for dep in &shape.dep_edges[s] {
            if let AbstractDep::External { pod: e, premise: u } = dep {
                for p in 1..target_pods {
                    for pp in 0..p {
                        model.add_constraint(constraint!(
                            uses_input[p][pp]
                                >= prove[s][p] + public_external[*u][pp]
                                    - uses_external[p][*e]
                                    - 1.0
                        ));
                    }
                }
            }
        }
    }

    // Constraint 8c: Forwarding an external premise as public also consumes an internal input
    // unless the forwarding POD uses the source external POD directly.
    for u in 0..num_external_premises {
        let e = shape.premise_pod[u];
        for p in 1..target_pods {
            for pp in 0..p {
                model.add_constraint(constraint!(
                    uses_input[p][pp]
                        >= public_external[u][p] + public_external[u][pp]
                            - uses_external[p][e]
                            - 1.0
                ));
            }
        }
    }

    // Constraint 8d: Total input PODs (internal + external) must not exceed max_input_pods
    // For each POD p, the total number of inputs is:
    // - Internal inputs: PODs pp < p that provide public statements used by p
    // - External inputs: User-provided PODs referenced by statements in p
    for p in 0..target_pods {
        let internal_sum: Expression = if p > 0 {
            (0..p).map(|pp| uses_input[p][pp]).sum()
        } else {
            0.into()
        };
        let external_sum: Expression = (0..num_external_pods).map(|e| uses_external[p][e]).sum();
        model.add_constraint(constraint!(
            internal_sum + external_sum <= (shape.params.max_input_pods as f64) * pod_used[p]
        ));
    }

    // Constraint 9: Symmetry breaking - use PODs in order
    // pod_used[p] >= pod_used[p+1]
    for p in 0..target_pods - 1 {
        model.add_constraint(constraint!(pod_used[p] >= pod_used[p + 1]));
    }

    // Solve
    let solve_started_at = Instant::now();
    let solution = match model.solve() {
        Ok(sol) => {
            log::debug!(
                "MILP(k={}) result=feasible solve_ms={} total_ms={}",
                target_pods,
                solve_started_at.elapsed().as_millis(),
                attempt_started_at.elapsed().as_millis()
            );
            sol
        }
        Err(err) => {
            let status = match err {
                ResolutionError::Infeasible => "infeasible",
                ResolutionError::Unbounded => "unbounded",
                ResolutionError::Other(_) | ResolutionError::Str(_) => "error",
            };
            log::debug!(
                "MILP(k={}) result={} solve_ms={} total_ms={} detail={}",
                target_pods,
                status,
                solve_started_at.elapsed().as_millis(),
                attempt_started_at.elapsed().as_millis(),
                err
            );
            // Infeasible or solver error with this number of PODs, try more
            return Ok(None);
        }
    };

    // Extract solution: count how many PODs are used.
    // Symmetry breaking (Constraint 9) ensures PODs are used in order with no gaps.
    let mut pod_count = 0;
    for p in 0..target_pods {
        if solution.value(pod_used[p]) > SOLVER_BINARY_THRESHOLD {
            pod_count += 1;
        }
    }

    let mut statement_to_pods: Vec<Vec<usize>> = vec![vec![]; n];
    let mut pod_statements: Vec<Vec<usize>> = vec![vec![]; pod_count];
    let mut pod_public_statements: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];
    let mut pod_internal_inputs: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];
    let mut pod_external_inputs: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];
    let mut pod_public_external_premises: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];

    for s in 0..n {
        for p in 0..pod_count {
            if solution.value(prove[s][p]) > SOLVER_BINARY_THRESHOLD {
                statement_to_pods[s].push(p);
                pod_statements[p].push(s);
            }
            if solution.value(public[s][p]) > SOLVER_BINARY_THRESHOLD {
                pod_public_statements[p].insert(s);
            }
        }
    }

    for p in 0..pod_count {
        for pp in 0..p {
            if solution.value(uses_input[p][pp]) > SOLVER_BINARY_THRESHOLD {
                pod_internal_inputs[p].insert(pp);
            }
        }
        for e in 0..num_external_pods {
            if solution.value(uses_external[p][e]) > SOLVER_BINARY_THRESHOLD {
                pod_external_inputs[p].insert(e);
            }
        }
    }

    for u in 0..num_external_premises {
        for p in 0..pod_count {
            if solution.value(public_external[u][p]) > SOLVER_BINARY_THRESHOLD {
                pod_public_external_premises[p].insert(u);
            }
        }
    }

    Ok(Some(OutputShape {
        pod_count,
        statement_to_pods,
        pod_statements,
        pod_public_statements,
        pod_internal_inputs,
        pod_external_inputs,
        pod_public_external_premises,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_external_shape(
        num_statements: usize,
        costs: Vec<StatementCost>,
        dep_edges: Vec<Vec<AbstractDep>>,
        output_public_indices: Vec<usize>,
        params: Params,
        max_pods: usize,
    ) -> InputShape {
        assert_eq!(costs.len(), num_statements);
        assert_eq!(dep_edges.len(), num_statements);
        InputShape {
            costs,
            dep_edges,
            output_public_indices,
            params,
            num_external_pods: 0,
            premise_pod: Vec::new(),
            max_pods,
        }
    }

    #[test]
    fn test_no_public_statements_error() {
        // At least one public statement is required - otherwise the POD can't
        // prove anything to an external verifier.
        let shape = no_external_shape(0, vec![], vec![], vec![], Params::default(), 20);
        let result = solve(&shape);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("No public statements requested"));
    }

    #[test]
    fn test_external_dependency_can_be_forwarded_to_reduce_input_pressure() {
        // Build a minimal synthetic case:
        // - s0 depends on external premise E
        // - s1 (output) depends on s0 and E
        // - max_input_pods = 1 and max_priv_statements = 1 forces two PODs:
        //   POD0 proves s0 and must make both s0 and E public,
        //   POD1 consumes only POD0 as input (no direct external input).
        let params = Params {
            max_statements: 3,
            max_public_statements: 2,
            max_input_pods: 1,
            ..Params::default()
        };

        let shape = InputShape {
            costs: vec![StatementCost::default(), StatementCost::default()],
            dep_edges: vec![
                vec![AbstractDep::External { pod: 0, premise: 0 }],
                vec![
                    AbstractDep::Internal(0),
                    AbstractDep::External { pod: 0, premise: 0 },
                ],
            ],
            output_public_indices: vec![1],
            params,
            num_external_pods: 1,
            premise_pod: vec![0],
            max_pods: 4,
        };

        let solution = solve(&shape).expect("solver should find a feasible forwarding layout");

        assert_eq!(solution.pod_count, 2);

        // POD1 should consume POD0 as its only input and avoid direct external input.
        assert!(solution.pod_internal_inputs[1].contains(&0));
        assert!(solution.pod_external_inputs[1].is_empty());

        // POD0 should expose the external premise publicly so POD1 can consume it via POD0.
        assert!(solution.pod_public_external_premises[0].contains(&0));
    }
}
