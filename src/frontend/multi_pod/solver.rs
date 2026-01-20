//! MILP solver for multi-POD packing.
//!
//! This module builds and solves a Mixed Integer Linear Program to minimize
//! the number of PODs needed to prove a set of statements.

// MILP constraint building uses explicit index loops for clarity
#![allow(clippy::needless_range_loop)]

use std::collections::BTreeSet;

use good_lp::{
    constraint, default_solver, variable, Expression, ProblemVariables, Solution, SolverModel,
    Variable,
};
use itertools::Itertools;

use super::Result;
use crate::{
    frontend::multi_pod::{
        cost::{AnchoredKeyId, CustomBatchId, StatementCost},
        deps::{DependencyGraph, StatementSource},
    },
    middleware::Params,
};

/// Threshold for interpreting MILP solver's floating-point results as binary.
/// The solver returns continuous values in [0, 1] for binary variables;
/// values > 0.5 are interpreted as "true" (1), otherwise "false" (0).
const SOLVER_BINARY_THRESHOLD: f64 = 0.5;

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
}

/// Input to the MILP solver.
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

    /// All unique anchored keys referenced by any statement.
    ///
    /// Each unique (dict, key) pair that is used as an anchored key reference
    /// in any operation. When a Contains statement with literal values is used
    /// as an argument, it creates an anchored key reference.
    pub all_anchored_keys: &'a [AnchoredKeyId],

    /// For each anchored key, the statement index that produces it (if any).
    ///
    /// When a Contains statement with literal (dict, key, value) args is explicitly
    /// added, it "produces" that anchored key. If the producer is in the same POD
    /// as statements using the anchored key, no auto-insertion is needed.
    /// `anchored_key_producers[i]` corresponds to `all_anchored_keys[i]`.
    pub anchored_key_producers: &'a [Option<usize>],

    /// Statement content groups for deduplication.
    ///
    /// Each inner Vec contains statement indices that have identical content.
    /// When multiple statements with the same content are proved in the same POD,
    /// they only use one statement slot (the POD deduplicates identical statements).
    pub statement_content_groups: &'a [Vec<usize>],
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

    // Collect all unique custom batch IDs used
    let all_batches: Vec<CustomBatchId> = input
        .costs
        .iter()
        .flat_map(|c| c.custom_batch_ids.iter().cloned())
        .unique()
        .collect();

    // Incremental approach: try solving with increasing POD counts
    // Start with min_pods and increment until we find a feasible solution
    for target_pods in min_pods..=input.max_pods {
        if let Some(solution) = try_solve_with_pods(input, n, target_pods, &all_batches)? {
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

/// Try to solve with exactly `target_pods` PODs.
/// Returns `Ok(Some(solution))` if feasible, `Ok(None)` if infeasible.
fn try_solve_with_pods(
    input: &SolverInput,
    n: usize,
    target_pods: usize,
    all_batches: &[CustomBatchId],
) -> Result<Option<MultiPodSolution>> {
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

    // batch_used[b][p] - custom batch b is used in POD p
    let batch_used: Vec<Vec<Variable>> = (0..all_batches.len())
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
    let anchored_key_used: Vec<Vec<Variable>> = (0..input.all_anchored_keys.len())
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

    // Collect all statement indices that are internal dependencies.
    // These are statements that other statements depend on, and may need to be copied
    // into PODs where the dependent statement is proved but the dependency is not.
    let internal_deps: BTreeSet<usize> = input
        .deps
        .statement_deps
        .iter()
        .flat_map(|deps| deps.iter())
        .filter_map(|dep| match dep {
            StatementSource::Internal(d) => Some(*d),
            StatementSource::External(_) => None,
        })
        .collect();

    // needs_copy[d][p] - dependency d needs to be copied into POD p
    // This is 1 when: (some statement s in p depends on d) AND (d is not proved in p)
    // We only create variables for dependencies that are actually used.
    let dep_indices: Vec<usize> = internal_deps.iter().copied().collect();
    let needs_copy: Vec<Vec<Variable>> = (0..dep_indices.len())
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // Collect all external POD hashes that statements depend on.
    // These are user-provided input PODs referenced by statements.
    use crate::middleware::Hash;
    let external_pods: Vec<Hash> = input
        .deps
        .statement_deps
        .iter()
        .flat_map(|deps| deps.iter())
        .filter_map(|dep| match dep {
            StatementSource::External(h) => Some(*h),
            StatementSource::Internal(_) => None,
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    // uses_external[p][e] - POD p uses external POD e as an input
    let uses_external: Vec<Vec<Variable>> = (0..target_pods)
        .map(|_| {
            (0..external_pods.len())
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // Map from external POD hash to index in uses_external
    let external_to_idx: std::collections::HashMap<Hash, usize> = external_pods
        .iter()
        .enumerate()
        .map(|(i, h)| (*h, i))
        .collect();

    // content_group_used[g][p] - content group g has at least one statement proved in POD p
    // When multiple statements have identical content, they share a slot in the POD.
    // This variable tracks whether at least one statement from each content group is proved.
    let num_groups = input.statement_content_groups.len();
    let content_group_used: Vec<Vec<Variable>> = (0..num_groups)
        .map(|_| {
            (0..target_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // Objective: minimize number of PODs used
    let objective: Expression = pod_used.iter().sum();
    let mut model = vars.minimise(objective).using(default_solver);

    // Constraint 1: Each statement must be proved at least once
    for s in 0..n {
        let sum: Expression = prove[s].iter().sum();
        model.add_constraint(constraint!(sum >= 1));
    }

    // Constraint 2: Output-public statements must be public in POD 0 (the output POD)
    // This ensures there's exactly one output POD, simplifying privacy guarantees.
    for &s in input.output_public_indices {
        model.add_constraint(constraint!(public[s][0] == 1));
    }

    // Constraint 2b: Non-output-public statements cannot be public in POD 0
    // This prevents private statements from leaking to the output POD's public slots.
    for s in 0..n {
        if !input.output_public_indices.contains(&s) {
            model.add_constraint(constraint!(public[s][0] == 0));
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

    // Constraint 5: Dependencies (works with Constraint 8 to enforce input POD tracking)
    //
    // If s depends on d (internal), and s is proved in p, then either:
    // - d is proved in p (local availability), OR
    // - d is public in some earlier POD p' < p (cross-POD availability)
    //
    // This constraint ensures dependencies are AVAILABLE. It does NOT track which
    // earlier PODs are actually used as inputs - that's handled by Constraint 8.
    // Together:
    // - Constraint 5 ensures the dependency CAN be satisfied
    // - Constraint 8 ensures that when we use a statement from earlier POD pp,
    //   we count pp as an input to pod p (for max_input_pods enforcement)
    for s in 0..n {
        for dep in &input.deps.statement_deps[s] {
            if let StatementSource::Internal(d) = dep {
                for p in 0..target_pods {
                    // prove[s][p] <= prove[d][p] + sum_{p' < p} public[d][p']
                    let mut rhs: Expression = prove[*d][p].into();
                    for pp in 0..p {
                        rhs += public[*d][pp];
                    }
                    model.add_constraint(constraint!(prove[s][p] <= rhs));
                }
            }
        }
    }

    // Constraint 5b: needs_copy tracking for cross-POD dependencies
    // needs_copy[d][p] = 1 when: some statement s proved in p depends on d, AND d is not proved in p.
    // This tracks CopyStatements that will be added during build_single_pod.
    for (di, &d) in dep_indices.iter().enumerate() {
        for p in 0..target_pods {
            // needs_copy[d][p] >= prove[s][p] - prove[d][p] for each s that depends on d
            // If s is in p (prove[s][p]=1) and d is not in p (prove[d][p]=0), then needs_copy >= 1
            for s in 0..n {
                let depends_on_d = input.deps.statement_deps[s]
                    .iter()
                    .any(|dep| matches!(dep, StatementSource::Internal(dep_d) if *dep_d == d));
                if depends_on_d {
                    model.add_constraint(constraint!(
                        needs_copy[di][p] >= prove[s][p] - prove[d][p]
                    ));
                }
            }

            // needs_copy[d][p] <= 1 - prove[d][p]
            // If d is proved locally (prove[d][p]=1), no copy needed (needs_copy <= 0)
            model.add_constraint(constraint!(needs_copy[di][p] <= 1 - prove[d][p]));
        }
    }

    // Constraint 6: Resource limits per POD
    //
    // 6a-pre: Content group tracking for statement deduplication
    // When multiple statement indices have identical content, they share a single slot in the POD.
    // content_group_used[g][p] = 1 iff at least one statement from group g is proved in POD p.
    for (g, group) in input.statement_content_groups.iter().enumerate() {
        for p in 0..target_pods {
            // Lower bound: if any statement in the group is proved, the group is used
            for &s in group {
                model.add_constraint(constraint!(content_group_used[g][p] >= prove[s][p]));
            }
            // Upper bound: if no statements in the group are proved, the group is not used
            let group_prove_sum: Expression = group.iter().map(|&s| prove[s][p]).sum();
            model.add_constraint(constraint!(content_group_used[g][p] <= group_prove_sum));
        }
    }

    for p in 0..target_pods {
        // 6a: Unique statement count (unique content groups + CopyStatements + anchored key Contains)
        // Statements with identical content share a slot, so we count content groups, not indices.
        // CopyStatements and anchored key Contains also use statement slots.
        // The total must not exceed max_priv_statements (= max_statements - max_public_statements).
        let unique_stmt_sum: Expression = (0..num_groups).map(|g| content_group_used[g][p]).sum();
        let copy_sum: Expression = (0..dep_indices.len()).map(|di| needs_copy[di][p]).sum();
        let anchored_key_sum: Expression = (0..input.all_anchored_keys.len())
            .map(|ak| anchored_key_used[ak][p])
            .sum();
        model.add_constraint(constraint!(
            unique_stmt_sum + copy_sum + anchored_key_sum
                <= (input.params.max_priv_statements() as f64) * pod_used[p]
        ));

        // 6b: Public statement count
        let pub_sum: Expression = (0..n).map(|s| public[s][p]).sum();
        model.add_constraint(constraint!(
            pub_sum <= (input.params.max_public_statements as f64) * pod_used[p]
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
    // batch_used[b][p] >= prove[s][p] for all s that use batch b (batch is used if any statement uses it)
    // batch_used[b][p] <= sum of prove[s][p] for all s using batch b (batch is 0 if no statements use it)
    for (b, batch_id) in all_batches.iter().enumerate() {
        for p in 0..target_pods {
            let mut sum: Expression = 0.into();
            for s in 0..n {
                if input.costs[s].custom_batch_ids.contains(batch_id) {
                    model.add_constraint(constraint!(batch_used[b][p] >= prove[s][p]));
                    sum += prove[s][p];
                }
            }
            model.add_constraint(constraint!(batch_used[b][p] <= sum));
        }
    }

    // Batch count per POD
    for p in 0..target_pods {
        let batch_sum: Expression = (0..all_batches.len()).map(|b| batch_used[b][p]).sum();
        model.add_constraint(constraint!(
            batch_sum <= (input.params.max_custom_predicate_batches as f64) * pod_used[p]
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
    for (ak_idx, ak) in input.all_anchored_keys.iter().enumerate() {
        let producer = input.anchored_key_producers[ak_idx];

        for p in 0..target_pods {
            let mut user_sum: Expression = 0.into();
            for s in 0..n {
                if input.costs[s].anchored_keys.contains(ak) {
                    if let Some(prod_idx) = producer {
                        // Producer exists: only count overhead if producer not in this POD
                        model.add_constraint(constraint!(
                            anchored_key_used[ak_idx][p] >= prove[s][p] - prove[prod_idx][p]
                        ));
                    } else {
                        // No producer: always need auto-insertion if user is present
                        model.add_constraint(constraint!(
                            anchored_key_used[ak_idx][p] >= prove[s][p]
                        ));
                    }
                    user_sum += prove[s][p];
                }
            }

            if let Some(prod_idx) = producer {
                // If producer is in POD, no auto-insertion needed (overhead = 0)
                model.add_constraint(constraint!(
                    anchored_key_used[ak_idx][p] <= 1 - prove[prod_idx][p]
                ));
            } else {
                // No producer: overhead is bounded by whether any user is present
                model.add_constraint(constraint!(anchored_key_used[ak_idx][p] <= user_sum));
            }
        }
    }

    // Constraint 8a: Internal input POD tracking using uses_input
    // uses_input[p][pp] >= prove[s][p] + public[d][pp] - prove[d][p] - 1
    // for each dependency (s depends on d)
    //
    // If s is proved in p and d is public in pp, we need pp as input UNLESS d is also
    // proved locally in p. Subtracting prove[d][p] ensures that when d is re-proved
    // locally (prove[d][p] = 1), the constraint becomes uses_input >= 0, which is
    // always satisfied without forcing the input relationship.
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

    // Constraint 8b: External input POD tracking using uses_external
    // If statement s is proved in POD p and s depends on external POD e, then uses_external[p][e] = 1
    for s in 0..n {
        for dep in &input.deps.statement_deps[s] {
            if let StatementSource::External(h) = dep {
                if let Some(&e) = external_to_idx.get(h) {
                    for p in 0..target_pods {
                        // If s is proved in p, then uses_external[p][e] = 1
                        model.add_constraint(constraint!(uses_external[p][e] >= prove[s][p]));
                    }
                }
            }
        }
    }

    // Total input PODs (internal + external) must not exceed max_input_pods
    // For POD 0: only external inputs (no earlier generated PODs exist)
    // For POD p > 0: internal inputs (earlier generated PODs) + external inputs
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
    let solution = match model.solve() {
        Ok(sol) => sol,
        Err(_) => {
            // Infeasible with this number of PODs, try more
            return Ok(None);
        }
    };

    // Extract solution
    let mut pod_count = 0;
    for p in 0..target_pods {
        if solution.value(pod_used[p]) > SOLVER_BINARY_THRESHOLD {
            pod_count = p + 1;
        }
    }

    let mut statement_to_pods: Vec<Vec<usize>> = vec![vec![]; n];
    let mut pod_statements: Vec<Vec<usize>> = vec![vec![]; pod_count];
    let mut pod_public_statements: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];

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

    Ok(Some(MultiPodSolution {
        pod_count,
        statement_to_pods,
        pod_statements,
        pod_public_statements,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_deps(n: usize) -> DependencyGraph {
        DependencyGraph {
            statement_deps: (0..n).map(|_| vec![]).collect(),
        }
    }

    #[test]
    fn test_simple_packing() {
        let params = Params {
            max_statements: 10,
            max_public_statements: 4,
            ..Params::default()
        };

        let costs: Vec<StatementCost> = (0..5).map(|_| StatementCost::default()).collect();
        let deps = make_simple_deps(5);
        let output_public = vec![0, 1];
        // Each statement is unique (its own content group)
        let content_groups: Vec<Vec<usize>> = (0..5).map(|i| vec![i]).collect();

        let input = SolverInput {
            num_statements: 5,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
            all_anchored_keys: &[],
            anchored_key_producers: &[],
            statement_content_groups: &content_groups,
        };

        let solution = solve(&input).unwrap();

        // Should fit in 1 POD
        assert_eq!(solution.pod_count, 1);
        assert_eq!(solution.pod_statements[0].len(), 5);
        assert!(solution.pod_public_statements[0].contains(&0));
        assert!(solution.pod_public_statements[0].contains(&1));
    }

    #[test]
    fn test_overflow_by_statements() {
        // max_priv_statements = max_statements - max_public_statements = 5 - 2 = 3
        let params = Params {
            max_statements: 5,
            max_public_statements: 2,
            ..Params::default()
        };

        let costs: Vec<StatementCost> = (0..6).map(|_| StatementCost::default()).collect();
        let deps = make_simple_deps(6);
        // At least one public statement is required
        let output_public: Vec<usize> = vec![0];
        // Each statement is unique (its own content group)
        let content_groups: Vec<Vec<usize>> = (0..6).map(|i| vec![i]).collect();

        let input = SolverInput {
            num_statements: 6,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
            all_anchored_keys: &[],
            anchored_key_producers: &[],
            statement_content_groups: &content_groups,
        };

        let solution = solve(&input).unwrap();

        // 6 statements / 3 per pod = exactly 2 PODs
        assert_eq!(solution.pod_count, 2);
    }

    #[test]
    fn test_no_public_statements_error() {
        // At least one public statement is required - otherwise the POD can't
        // prove anything to an external verifier.
        let params = Params::default();
        let costs: Vec<StatementCost> = vec![];
        let deps = make_simple_deps(0);
        let output_public: Vec<usize> = vec![];

        let content_groups: Vec<Vec<usize>> = vec![];
        let input = SolverInput {
            num_statements: 0,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
            all_anchored_keys: &[],
            anchored_key_producers: &[],
            statement_content_groups: &content_groups,
        };

        let result = solve(&input);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("No public statements requested"));
    }
}
