//! MILP solver for multi-POD packing.
//!
//! This module builds and solves a Mixed Integer Linear Program (MILP) to minimize
//! the number of PODs needed to prove a set of statements while respecting resource
//! limits and dependency constraints.
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
//! - **Constraint 8d (Input Limit)**: Total inputs (internal + external) ≤ max_input_pods.
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

use std::{
    collections::{BTreeSet, HashMap},
    time::Instant,
};

use good_lp::{
    constraint, default_solver, variable, Expression, ProblemVariables, ResolutionError, Solution,
    SolverModel, Variable,
};
use itertools::Itertools;

use super::Result;
use crate::{
    frontend::multi_pod::{
        cost::{CustomPredicateId, StatementCost},
        deps::{DependencyGraph, ExternalDependency, StatementSource},
    },
    middleware::{Hash, Params},
};

/// Threshold for interpreting MILP solver's floating-point results as binary.
/// The solver returns continuous values in [0, 1] for binary variables;
/// values > 0.5 are interpreted as "true" (1), otherwise "false" (0).
const SOLVER_BINARY_THRESHOLD: f64 = 0.5;

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
    // anchored_key_memberships: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct ModelSizeEstimate {
    vars_prove: usize,
    vars_public: usize,
    vars_public_external: usize,
    vars_pod_used: usize,
    vars_batch_used: usize,
    // vars_anchored_key_used: usize,
    vars_uses_input: usize,
    vars_uses_external: usize,
    // vars_content_group_used: usize,
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
    // c7b_anchored_key_tracking: usize,
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
        input: &SolverInput,
        target_pods: usize,
        all_batches_len: usize,
        external_pods_len: usize,
        external_premises_len: usize,
        debug_ctx: &SolveDebugContext,
    ) -> Self {
        let n = input.num_statements;
        // let num_groups = input.statement_content_groups.len();
        // let num_anchored_keys = input.all_anchored_keys.len();
        let triangular_k = target_pods * target_pods.saturating_sub(1) / 2;

        let vars_prove = n * target_pods;
        let vars_public = n * target_pods;
        let vars_public_external = external_premises_len * target_pods;
        let vars_pod_used = target_pods;
        let vars_batch_used = all_batches_len * target_pods;
        // let vars_anchored_key_used = num_anchored_keys * target_pods;
        let vars_uses_input = triangular_k;
        let vars_uses_external = external_pods_len * target_pods;
        // let vars_content_group_used = num_groups * target_pods;
        let vars_total = vars_prove
            + vars_public
            + vars_public_external
            + vars_pod_used
            + vars_batch_used
            // + vars_anchored_key_used
            + vars_uses_input
            + vars_uses_external;
        // + vars_content_group_used;

        let c1_coverage = n;
        let c2_output_public = input.output_public_indices.len();
        let c2b_output_privacy = n.saturating_sub(c2_output_public);
        let c3_public_implies_proved = n * target_pods;
        let c4_pod_existence = n * target_pods;
        let c5_internal_dependencies = debug_ctx.dep_stats.internal_edges * target_pods;
        let c5_external_dependencies = debug_ctx.dep_stats.external_edges * target_pods;
        let c6_pre_content_group = n * target_pods; // + (num_groups * target_pods);
        let c6_resource_limits = 7 * target_pods;
        let c7_batch_cardinality =
            (debug_ctx.batch_memberships * target_pods) + (all_batches_len * target_pods);
        // let c7b_anchored_key_tracking =
        //     (debug_ctx.anchored_key_memberships * target_pods) + (num_anchored_keys * target_pods);
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
            // + c7b_anchored_key_tracking
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
            // vars_anchored_key_used,
            vars_uses_input,
            vars_uses_external,
            // vars_content_group_used,
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
            // c7b_anchored_key_tracking,
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

fn dependency_stats(deps: &DependencyGraph) -> DependencyStats {
    let mut stats = DependencyStats::default();
    for dep_list in &deps.statement_deps {
        for dep in dep_list {
            match dep {
                StatementSource::Internal(_) => stats.internal_edges += 1,
                StatementSource::External(_) => stats.external_edges += 1,
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

/// Solution from the MILP solver.
#[derive(Clone, Debug)]
pub struct MultiPodSolution {
    /// Number of PODs needed.
    pub pod_count: usize,

    /// For each statement index, which POD(s) it is proved in.
    /// (A statement may be proved in multiple PODs if re-proving is cheaper than copying.)
    pub statement_to_pods: Vec<Vec<usize>>,

    /// For each POD, which statement indices are proved in it.
    pub pod_statements: Vec<Vec<usize>>,

    /// For each POD, which statement indices are public in it.
    pub pod_public_statements: Vec<BTreeSet<usize>>,

    /// For each POD, which earlier internal PODs are used as inputs.
    pub pod_internal_inputs: Vec<BTreeSet<usize>>,

    /// External input POD hashes referenced by the solution.
    /// `pod_external_inputs[*]` stores indices into this vector.
    pub external_pod_hashes: Vec<Hash>,

    /// For each POD, which external input PODs are used as inputs.
    /// Indices are into `external_pod_hashes`.
    pub pod_external_inputs: Vec<BTreeSet<usize>>,

    /// Unique external premises referenced by statement dependencies.
    pub external_premises: Vec<ExternalDependency>,

    /// For each POD, which external premises are exposed as public statements.
    /// Indices are into `external_premises`.
    pub pod_public_external_premises: Vec<BTreeSet<usize>>,
}

/// Input to the MILP solver.
#[derive(Debug)]
pub struct SolverInput<'a> {
    /// Number of statements.
    pub num_statements: usize,

    /// Resource costs for each statement.
    pub costs: &'a [StatementCost],

    /// Dependency graph.
    pub deps: &'a DependencyGraph,

    /// Indices of statements that must be public in output PODs.
    pub output_public_indices: &'a [usize],

    /// Parameters defining per-POD limits.
    pub params: &'a Params,

    /// Maximum number of PODs the solver will consider.
    pub max_pods: usize,
    // /// All unique anchored keys referenced by any statement.
    // ///
    // /// Each unique (dict, key) pair that is used as an anchored key reference
    // /// in any operation. When a Contains statement with literal values is used
    // /// as an argument, it creates an anchored key reference.
    // pub all_anchored_keys: &'a [AnchoredKeyId],

    // /// For each anchored key, the statement index that produces it (if any).
    // ///
    // /// When a Contains statement with literal (dict, key, value) args is explicitly
    // /// added, it "produces" that anchored key. If the producer is in the same POD
    // /// as statements using the anchored key, no auto-insertion is needed.
    // /// `anchored_key_producers[i]` corresponds to `all_anchored_keys[i]`.
    // pub anchored_key_producers: &'a [Option<usize>],
    // /// Statement content groups for deduplication.
    // ///
    // /// Each inner Vec contains statement indices that have identical content.
    // /// When multiple statements with the same content are proved in the same POD,
    // /// they only use one statement slot (the POD deduplicates identical statements).
    // pub statement_content_groups: &'a [Vec<usize>],
}

/// Solve the MILP problem to find optimal POD packing.
///
/// Uses an incremental approach: tries solving with min_pods first,
/// then increments until a solution is found or target_pods is exceeded.
/// This is efficient for the common case where min_pods is sufficient.
pub fn solve(input: &SolverInput) -> Result<MultiPodSolution> {
    let n = input.num_statements;

    // Require at least one public statement. A POD with no public statements
    // can't prove anything to an external verifier.
    if input.output_public_indices.is_empty() {
        return Err(super::Error::Solver(
            "No public statements requested. Use pub_op() to add at least one statement \
             that should be visible in the output POD."
                .to_string(),
        ));
    }

    // Check that all output-public statements can fit in a single POD
    let num_output_public = input.output_public_indices.len();
    if num_output_public > input.params.max_public_statements {
        return Err(super::Error::Solver(format!(
            "Too many public statements requested: {} requested, but max_public_statements is {}. \
             All public statements must fit in a single output POD.",
            num_output_public, input.params.max_public_statements
        )));
    }

    // Lower bound on number of PODs needed
    // Note: max_priv_statements is the limit on total unique statements per POD
    // (public statements are copies from private slots)
    let max_stmts_per_pod = input.params.max_priv_statements();
    let min_pods_by_statements = n.div_ceil(max_stmts_per_pod);
    let min_pods = min_pods_by_statements.max(1);

    // Check if the problem exceeds the configured max_pods limit
    if min_pods > input.max_pods {
        return Err(super::Error::Solver(format!(
            "Problem requires at least {} PODs, but max_pods is set to {}. \
             Increase Options::max_pods to allow more PODs.",
            min_pods, input.max_pods
        )));
    }

    // Collect all unique custom predicate IDs used
    let all_custom_predicates: Vec<CustomPredicateId> = input
        .costs
        .iter()
        .flat_map(|c| c.custom_predicates_ids.iter().cloned())
        .unique()
        .collect();

    // Collect all unique external POD hashes and external premises referenced by dependencies.
    let mut external_pods: Vec<Hash> = Vec::new();
    let mut external_pod_to_idx: HashMap<Hash, usize> = HashMap::new();
    let mut external_premises: Vec<ExternalDependency> = Vec::new();
    let mut external_premise_to_idx: HashMap<ExternalDependency, usize> = HashMap::new();
    for deps in &input.deps.statement_deps {
        for dep in deps {
            if let StatementSource::External(ext) = dep {
                if let std::collections::hash_map::Entry::Vacant(e) =
                    external_pod_to_idx.entry(ext.pod_hash)
                {
                    e.insert(external_pods.len());
                    external_pods.push(ext.pod_hash);
                }
                if !external_premise_to_idx.contains_key(ext) {
                    external_premise_to_idx.insert(ext.clone(), external_premises.len());
                    external_premises.push(ext.clone());
                }
            }
        }
    }

    let dep_stats = dependency_stats(input.deps);
    let batch_memberships: usize = input
        .costs
        .iter()
        .map(|c| c.custom_predicates_ids.len())
        .sum();
    // let anchored_key_memberships: usize = input.costs.iter().map(|c| c.anchored_keys.len()).sum();
    let debug_ctx = SolveDebugContext {
        dep_stats,
        batch_memberships,
        // anchored_key_memberships,
    };

    if log::log_enabled!(log::Level::Debug) {
        let resource_totals = ResourceTotals::from_costs(input.costs);
        let lb_statement_groups = lower_bound_from_total(input.num_statements, max_stmts_per_pod);
        let lb_merkle = lower_bound_from_total(
            resource_totals.merkle_proofs,
            input.params.max_merkle_proofs_containers,
        );
        let lb_merkle_transitions = lower_bound_from_total(
            resource_totals.merkle_state_transitions,
            input
                .params
                .max_merkle_tree_state_transition_proofs_containers,
        );
        let lb_custom_pred_verifications = lower_bound_from_total(
            resource_totals.custom_pred_verifications,
            input.params.max_custom_predicate_verifications,
        );
        let lb_signed_by =
            lower_bound_from_total(resource_totals.signed_by, input.params.max_signed_by);
        let lb_public_key_of = lower_bound_from_total(
            resource_totals.public_key_of,
            input.params.max_public_key_of,
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
            // input.statement_content_groups.len(),
            // input.all_anchored_keys.len(),
            all_custom_predicates.len(),
            dep_stats.internal_edges,
            dep_stats.external_edges,
            external_pods.len(),
            external_premises.len(),
            min_pods,
            input.max_pods
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
            // anchored_key_memberships
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
    for target_pods in min_pods..=input.max_pods {
        log::debug!("Trying to solve with {} PODs", target_pods);
        if let Some(solution) = try_solve_with_pods(
            input,
            target_pods,
            &all_custom_predicates,
            &external_pods,
            &external_premises,
            &debug_ctx,
        )? {
            return Ok(solution);
        }
        // Infeasible with target_pods, try more
    }

    // No feasible solution found even with max_pods
    Err(super::Error::Solver(format!(
        "No feasible solution found with up to {} PODs",
        input.max_pods
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
    input: &SolverInput,
    target_pods: usize,
    all_custom_predicates: &[CustomPredicateId],
    external_pods: &[Hash],
    external_premises: &[ExternalDependency],
    debug_ctx: &SolveDebugContext,
) -> Result<Option<MultiPodSolution>> {
    let attempt_started_at = Instant::now();

    // Create variables
    let mut vars = ProblemVariables::new();
    let n = input.num_statements;

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

    // anchored_key_used[ak][p] - anchored key ak is used in POD p
    // When a statement references an anchored key (via a Contains statement argument),
    // that POD must have a Contains statement for that (dict, key) pair.
    // MainPodBuilder::add_entries_contains auto-inserts these, and we must account
    // for them in the statement count.
    // let anchored_key_used: Vec<Vec<Variable>> = (0..input.all_anchored_keys.len())
    //     .map(|_| {
    //         (0..target_pods)
    //             .map(|_| vars.add(variable().binary()))
    //             .collect()
    //     })
    //     .collect();

    // uses_input[p][pp] - POD p uses POD pp as an input (pp < p)
    // We only create variables for pp < p
    let uses_input: Vec<Vec<Variable>> = (0..target_pods)
        .map(|p| (0..p).map(|_| vars.add(variable().binary())).collect())
        .collect();

    // uses_external[p][e] - POD p uses external POD e as an input
    let uses_external: Vec<Vec<Variable>> = (0..target_pods)
        .map(|_| {
            (0..external_pods.len())
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // public_external[u][p] - external premise u is exposed publicly in POD p
    let public_external: Vec<Vec<Variable>> = (0..external_premises.len())
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // Map from external POD hash to index in uses_external
    let external_to_idx: HashMap<Hash, usize> = external_pods
        .iter()
        .enumerate()
        .map(|(i, h)| (*h, i))
        .collect();

    let external_premise_to_idx: HashMap<ExternalDependency, usize> = external_premises
        .iter()
        .enumerate()
        .map(|(i, ext)| (ext.clone(), i))
        .collect();

    // content_group_used[g][p] - content group g has at least one statement proved in POD p
    // When multiple statements have identical content, they share a slot in the POD.
    // This variable tracks whether at least one statement from each content group is proved.
    // let num_groups = input.statement_content_groups.len();
    // let content_group_used: Vec<Vec<Variable>> = (0..num_groups)
    //     .map(|_| {
    //         (0..target_pods)
    //             .map(|_| vars.add(variable().binary()))
    //             .collect()
    //     })
    //     .collect();

    if log::log_enabled!(log::Level::Debug) {
        let estimate = ModelSizeEstimate::for_target_pods(
            input,
            target_pods,
            all_custom_predicates.len(),
            external_pods.len(),
            external_premises.len(),
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
            // estimate.vars_anchored_key_used,
            estimate.vars_uses_input,
            estimate.vars_uses_external,
            // estimate.vars_content_group_used
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
            // estimate.c7b_anchored_key_tracking,
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
    for &s in input.output_public_indices {
        model.add_constraint(constraint!(public[s][output_pod] == 1));
    }

    // Constraint 2b: Non-output-public statements cannot be public in the output POD
    // This prevents private statements from leaking to the output POD's public slots.
    for s in 0..n {
        if !input.output_public_indices.contains(&s) {
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
        for dep in &input.deps.statement_deps[s] {
            match dep {
                StatementSource::Internal(d) => {
                    for p in 0..target_pods {
                        let mut rhs: Expression = prove[*d][p].into();
                        for pp in 0..p {
                            rhs += public[*d][pp];
                        }
                        model.add_constraint(constraint!(prove[s][p] <= rhs));
                    }
                }
                StatementSource::External(ext) => {
                    if let (Some(&e), Some(&u)) = (
                        external_to_idx.get(&ext.pod_hash),
                        external_premise_to_idx.get(ext),
                    ) {
                        for p in 0..target_pods {
                            let mut rhs: Expression = uses_external[p][e].into();
                            for pp in 0..p {
                                rhs += public_external[u][pp];
                            }
                            model.add_constraint(constraint!(prove[s][p] <= rhs));
                        }
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
    for (u, ext) in external_premises.iter().enumerate() {
        if let Some(&e) = external_to_idx.get(&ext.pod_hash) {
            for p in 0..target_pods {
                let mut rhs: Expression = uses_external[p][e].into();
                for pp in 0..p {
                    rhs += public_external[u][pp];
                }
                model.add_constraint(constraint!(public_external[u][p] <= rhs));
                model.add_constraint(constraint!(public_external[u][p] <= pod_used[p]));
            }
        }
    }

    // Constraint 6: Resource limits per POD
    //
    // 6a-pre: Content group tracking for statement deduplication
    // When multiple statement indices have identical content, they share a single slot in the POD.
    // content_group_used[g][p] = 1 iff at least one statement from group g is proved in POD p.
    // for (g, group) in input.statement_content_groups.iter().enumerate() {
    //     for p in 0..target_pods {
    //         // Lower bound: if any statement in the group is proved, the group is used
    //         for &s in group {
    //             model.add_constraint(constraint!(content_group_used[g][p] >= prove[s][p]));
    //         }
    //         // Upper bound: if no statements in the group are proved, the group is not used
    //         let group_prove_sum: Expression = group.iter().map(|&s| prove[s][p]).sum();
    //         model.add_constraint(constraint!(content_group_used[g][p] <= group_prove_sum));
    //     }
    // }

    for p in 0..target_pods {
        // 6a: Statement count
        // // Anchored key Contains statements are auto-inserted by MainPodBuilder when needed.
        // // The total must not exceed max_priv_statements (= max_statements - max_public_statements).
        let stmt_sum: Expression = (0..n).map(|g| prove[g][p]).sum();
        // let anchored_key_sum: Expression = (0..input.all_anchored_keys.len())
        //     .map(|ak| anchored_key_used[ak][p])
        //     .sum();
        model.add_constraint(constraint!(
            stmt_sum <= (input.params.max_priv_statements() as f64) * pod_used[p]
        ));

        // 6b: Public statement count (internal public statements + forwarded external premises)
        let pub_sum_internal: Expression = (0..n).map(|s| public[s][p]).sum();
        let pub_sum_external: Expression = (0..external_premises.len())
            .map(|u| public_external[u][p])
            .sum();
        model.add_constraint(constraint!(
            pub_sum_internal + pub_sum_external
                <= (input.params.max_public_statements as f64) * pod_used[p]
        ));

        // 6c: Merkle proofs
        let merkle_sum: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_proofs as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            merkle_sum <= (input.params.max_merkle_proofs_containers as f64) * pod_used[p]
        ));

        // 6d: Merkle state transitions
        let mst_sum: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_state_transitions as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            mst_sum
                <= (input
                    .params
                    .max_merkle_tree_state_transition_proofs_containers as f64)
                    * pod_used[p]
        ));

        // 6e: Custom predicate verifications
        let cpv_sum: Expression = (0..n)
            .map(|s| (input.costs[s].custom_pred_verifications as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            cpv_sum <= (input.params.max_custom_predicate_verifications as f64) * pod_used[p]
        ));

        // 6f: SignedBy
        let sb_sum: Expression = (0..n)
            .map(|s| (input.costs[s].signed_by as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            sb_sum <= (input.params.max_signed_by as f64) * pod_used[p]
        ));

        // 6g: PublicKeyOf
        let pko_sum: Expression = (0..n)
            .map(|s| (input.costs[s].public_key_of as f64) * prove[s][p])
            .sum();
        model.add_constraint(constraint!(
            pko_sum <= (input.params.max_public_key_of as f64) * pod_used[p]
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
                if input.costs[s].custom_predicates_ids.contains(predicate_id) {
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
            custom_predicate_sum <= (input.params.max_custom_predicates as f64) * pod_used[p]
        ));
    }

    // Constraint 7b: Anchored key tracking
    //
    // anchored_key_used[ak][p] = 1 when auto-insertion of a Contains is needed for anchored key ak in POD p.
    // This happens when: some statement using ak is in POD p, AND the producing Contains is NOT in POD p.
    //
    // If a Contains statement explicitly produces ak (anchored_key_producers[ak] = Some(prod_idx)):
    //   - Lower: anchored_key_used[ak][p] >= prove[s][p] - prove[prod_idx][p] for all s using ak
    //   - Upper: anchored_key_used[ak][p] <= 1 - prove[prod_idx][p]
    //   This ensures overhead is 0 when the producer is in the same POD.
    //
    // If no Contains produces ak (anchored_key_producers[ak] = None):
    //   - Lower: anchored_key_used[ak][p] >= prove[s][p] for all s using ak
    //   - Upper: anchored_key_used[ak][p] <= sum of prove[s][p] for all s using ak
    //   Auto-insertion is always needed when any user is present.
    // for (ak_idx, ak) in input.all_anchored_keys.iter().enumerate() {
    //     let producer = input.anchored_key_producers[ak_idx];

    //     for p in 0..target_pods {
    //         let mut user_sum: Expression = 0.into();
    //         for s in 0..n {
    //             if input.costs[s].anchored_keys.contains(ak) {
    //                 if let Some(prod_idx) = producer {
    //                     // Producer exists: only count overhead if producer not in this POD
    //                     model.add_constraint(constraint!(
    //                         anchored_key_used[ak_idx][p] >= prove[s][p] - prove[prod_idx][p]
    //                     ));
    //                 } else {
    //                     // No producer: always need auto-insertion if user is present
    //                     model.add_constraint(constraint!(
    //                         anchored_key_used[ak_idx][p] >= prove[s][p]
    //                     ));
    //                 }
    //                 user_sum += prove[s][p];
    //             }
    //         }

    //         if let Some(prod_idx) = producer {
    //             // If producer is in POD, no auto-insertion needed (overhead = 0)
    //             model.add_constraint(constraint!(
    //                 anchored_key_used[ak_idx][p] <= 1 - prove[prod_idx][p]
    //             ));
    //         } else {
    //             // No producer: overhead is bounded by whether any user is present
    //             model.add_constraint(constraint!(anchored_key_used[ak_idx][p] <= user_sum));
    //         }
    //     }
    // }

    // Constraint 8a: Internal input POD tracking using uses_input.
    // If s is proved in p and depends on internal d exposed by pp, then pp must be counted
    // as an input unless d is also proved locally in p.
    for s in 0..n {
        for dep in &input.deps.statement_deps[s] {
            if let StatementSource::Internal(d) = dep {
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
        for dep in &input.deps.statement_deps[s] {
            if let StatementSource::External(ext) = dep {
                if let (Some(&e), Some(&u)) = (
                    external_to_idx.get(&ext.pod_hash),
                    external_premise_to_idx.get(ext),
                ) {
                    for p in 1..target_pods {
                        for pp in 0..p {
                            model.add_constraint(constraint!(
                                uses_input[p][pp]
                                    >= prove[s][p] + public_external[u][pp]
                                        - uses_external[p][e]
                                        - 1.0
                            ));
                        }
                    }
                }
            }
        }
    }

    // Constraint 8c: Forwarding an external premise as public also consumes an internal input
    // unless the forwarding POD uses the source external POD directly.
    for (u, ext) in external_premises.iter().enumerate() {
        if let Some(&e) = external_to_idx.get(&ext.pod_hash) {
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
        let external_sum: Expression = (0..external_pods.len()).map(|e| uses_external[p][e]).sum();
        model.add_constraint(constraint!(
            internal_sum + external_sum <= (input.params.max_input_pods as f64) * pod_used[p]
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
        for e in 0..external_pods.len() {
            if solution.value(uses_external[p][e]) > SOLVER_BINARY_THRESHOLD {
                pod_external_inputs[p].insert(e);
            }
        }
    }

    for u in 0..external_premises.len() {
        for p in 0..pod_count {
            if solution.value(public_external[u][p]) > SOLVER_BINARY_THRESHOLD {
                pod_public_external_premises[p].insert(u);
            }
        }
    }

    Ok(Some(MultiPodSolution {
        pod_count,
        statement_to_pods,
        pod_statements,
        pod_public_statements,
        pod_internal_inputs,
        external_pod_hashes: external_pods.to_vec(),
        pod_external_inputs,
        external_premises: external_premises.to_vec(),
        pod_public_external_premises,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        frontend::multi_pod::deps::ExternalDependency,
        middleware::{Statement, Value, ValueRef},
    };

    #[test]
    fn test_no_public_statements_error() {
        // At least one public statement is required - otherwise the POD can't
        // prove anything to an external verifier.
        let params = Params::default();
        let deps = DependencyGraph {
            statement_deps: vec![],
        };

        let input = SolverInput {
            num_statements: 0,
            costs: &[],
            deps: &deps,
            output_public_indices: &[],
            params: &params,
            max_pods: 20,
            // all_anchored_keys: &[],
            // anchored_key_producers: &[],
            // statement_content_groups: &[],
        };

        let result = solve(&input);
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

        let ext_stmt = Statement::Equal(
            ValueRef::Literal(Value::from(42_i64)),
            ValueRef::Literal(Value::from(42_i64)),
        );
        let external_dep = ExternalDependency {
            pod_hash: Hash::default(),
            statement: ext_stmt,
        };

        let deps = DependencyGraph {
            statement_deps: vec![
                vec![StatementSource::External(external_dep.clone())],
                vec![
                    StatementSource::Internal(0),
                    StatementSource::External(external_dep),
                ],
            ],
        };

        let costs = vec![StatementCost::default(), StatementCost::default()];
        // let statement_content_groups = vec![vec![0], vec![1]];
        let output_public = vec![1];

        let input = SolverInput {
            num_statements: 2,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 4,
            // all_anchored_keys: &[],
            // anchored_key_producers: &[],
            // statement_content_groups: &statement_content_groups,
        };

        let solution = solve(&input).expect("solver should find a feasible forwarding layout");

        assert_eq!(solution.pod_count, 2);
        assert_eq!(solution.external_premises.len(), 1);

        // POD1 should consume POD0 as its only input and avoid direct external input.
        assert!(solution.pod_internal_inputs[1].contains(&0));
        assert!(solution.pod_external_inputs[1].is_empty());

        // POD0 should expose the external premise publicly so POD1 can consume it via POD0.
        assert!(solution.pod_public_external_premises[0].contains(&0));
    }
}
