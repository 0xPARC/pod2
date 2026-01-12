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

use super::Result;
use crate::{
    frontend::multi_pod::{
        cost::{CustomBatchId, StatementCost},
        deps::{DependencyGraph, StatementSource},
    },
    middleware::Params,
};

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

    /// Order to prove PODs (respects dependencies - earlier PODs first).
    pub prove_order: Vec<usize>,

    /// Which PODs are "output" PODs (contain user-requested public statements).
    pub output_pod_indices: BTreeSet<usize>,
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
    pub output_public_indices: &'a BTreeSet<usize>,

    /// Parameters defining per-POD limits.
    pub params: &'a Params,

    /// Maximum number of PODs the solver will consider.
    pub max_pods: usize,
}

/// Solve the MILP problem to find optimal POD packing.
pub fn solve(input: &SolverInput) -> Result<MultiPodSolution> {
    let n = input.num_statements;
    if n == 0 {
        return Ok(MultiPodSolution {
            pod_count: 0,
            statement_to_pods: vec![],
            pod_statements: vec![],
            pod_public_statements: vec![],
            prove_order: vec![],
            output_pod_indices: BTreeSet::new(),
        });
    }

    // Check that all output-public statements can fit in a single POD
    // This simplifies the privacy model: POD 0 is the only output POD.
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

    // Upper bound: add slack but cap at configured max_pods
    let max_pods = (min_pods * 2).max(2).min(n).min(input.max_pods);

    // Collect all custom batch IDs used (BTreeSet for deterministic ordering)
    let all_batches: Vec<CustomBatchId> = input
        .costs
        .iter()
        .flat_map(|c| c.custom_batch_ids.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    // Create variables
    let mut vars = ProblemVariables::new();

    // prove[s][p] - statement s is proved in POD p
    let prove: Vec<Vec<Variable>> = (0..n)
        .map(|_| {
            (0..max_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // public[s][p] - statement s is public in POD p
    let public: Vec<Vec<Variable>> = (0..n)
        .map(|_| {
            (0..max_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // pod_used[p] - POD p is used
    let pod_used: Vec<Variable> = (0..max_pods)
        .map(|_| vars.add(variable().binary()))
        .collect();

    // batch_used[b][p] - custom batch b is used in POD p
    let batch_used: Vec<Vec<Variable>> = (0..all_batches.len())
        .map(|_| {
            (0..max_pods)
                .map(|_| vars.add(variable().binary()))
                .collect()
        })
        .collect();

    // uses_input[p][pp] - POD p uses POD pp as an input (pp < p)
    // We only create variables for pp < p
    let uses_input: Vec<Vec<Variable>> = (0..max_pods)
        .map(|p| (0..p).map(|_| vars.add(variable().binary())).collect())
        .collect();

    // Objective: minimize number of PODs used
    let objective: Expression = pod_used.iter().sum();
    let mut model = vars.minimise(objective).using(default_solver);

    // Constraint 1: Each statement must be proved at least once
    for s in 0..n {
        let sum: Expression = prove[s].iter().sum();
        model = model.with(constraint!(sum >= 1));
    }

    // Constraint 2: Output-public statements must be public in POD 0 (the output POD)
    // This ensures there's exactly one output POD, simplifying privacy guarantees.
    for &s in input.output_public_indices {
        model = model.with(constraint!(public[s][0] == 1));
    }

    // Constraint 2b: Non-output-public statements cannot be public in POD 0
    // This prevents private statements from leaking to the output POD's public slots.
    for s in 0..n {
        if !input.output_public_indices.contains(&s) {
            model = model.with(constraint!(public[s][0] == 0));
        }
    }

    // Constraint 3: Public implies proved
    for s in 0..n {
        for p in 0..max_pods {
            model = model.with(constraint!(public[s][p] <= prove[s][p]));
        }
    }

    // Constraint 4: Pod existence - if any statement is proved in p, p is used
    for s in 0..n {
        for p in 0..max_pods {
            model = model.with(constraint!(prove[s][p] <= pod_used[p]));
        }
    }

    // Constraint 5: Dependencies
    // If s depends on d (internal), and s is proved in p, then either:
    // - d is proved in p, OR
    // - d is public in some earlier POD p' < p
    for s in 0..n {
        for dep in &input.deps.statement_deps[s].depends_on {
            if let StatementSource::Internal(d) = dep {
                for p in 0..max_pods {
                    // prove[s][p] <= prove[d][p] + sum_{p' < p} public[d][p']
                    let mut rhs: Expression = prove[*d][p].into();
                    for pp in 0..p {
                        rhs += public[*d][pp];
                    }
                    model = model.with(constraint!(prove[s][p] <= rhs));
                }
            }
        }
    }

    // Constraint 6: Resource limits per POD
    for p in 0..max_pods {
        // 6a: Total statement count (all statements are proved in private slots,
        // public statements are then copied to public slots)
        let stmt_sum: Expression = (0..n).map(|s| prove[s][p]).sum();
        model = model.with(constraint!(
            stmt_sum <= (input.params.max_priv_statements() as f64) * pod_used[p]
        ));

        // 6b: Public statement count
        let pub_sum: Expression = (0..n).map(|s| public[s][p]).sum();
        model = model.with(constraint!(
            pub_sum <= (input.params.max_public_statements as f64) * pod_used[p]
        ));

        // 6c: Merkle proofs
        let merkle_sum: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_proofs as f64) * prove[s][p])
            .sum();
        model = model.with(constraint!(
            merkle_sum <= (input.params.max_merkle_proofs_containers as f64) * pod_used[p]
        ));

        // 6d: Merkle state transitions
        let mst_sum: Expression = (0..n)
            .map(|s| (input.costs[s].merkle_state_transitions as f64) * prove[s][p])
            .sum();
        model = model.with(constraint!(
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
        model = model.with(constraint!(
            cpv_sum <= (input.params.max_custom_predicate_verifications as f64) * pod_used[p]
        ));

        // 6f: SignedBy
        let sb_sum: Expression = (0..n)
            .map(|s| (input.costs[s].signed_by as f64) * prove[s][p])
            .sum();
        model = model.with(constraint!(
            sb_sum <= (input.params.max_signed_by as f64) * pod_used[p]
        ));

        // 6g: PublicKeyOf
        let pko_sum: Expression = (0..n)
            .map(|s| (input.costs[s].public_key_of as f64) * prove[s][p])
            .sum();
        model = model.with(constraint!(
            pko_sum <= (input.params.max_public_key_of as f64) * pod_used[p]
        ));
    }

    // Constraint 7: Batch cardinality
    // batch_used[b][p] >= prove[s][p] for all s that use batch b
    for (b, batch_id) in all_batches.iter().enumerate() {
        for p in 0..max_pods {
            for s in 0..n {
                if input.costs[s].custom_batch_ids.contains(batch_id) {
                    model = model.with(constraint!(batch_used[b][p] >= prove[s][p]));
                }
            }
        }
    }

    // batch_used[b][p] <= sum of prove[s][p] for all s using batch b
    // (ensures batch_used is 0 if no statements use it)
    for (b, batch_id) in all_batches.iter().enumerate() {
        for p in 0..max_pods {
            let sum: Expression = (0..n)
                .filter(|&s| input.costs[s].custom_batch_ids.contains(batch_id))
                .map(|s| prove[s][p])
                .sum();
            model = model.with(constraint!(batch_used[b][p] <= sum));
        }
    }

    // Batch count per POD
    for p in 0..max_pods {
        let batch_sum: Expression = (0..all_batches.len()).map(|b| batch_used[b][p]).sum();
        model = model.with(constraint!(
            batch_sum <= (input.params.max_custom_predicate_batches as f64) * pod_used[p]
        ));
    }

    // Constraint 8: Input POD limits using uses_input
    // uses_input[p][pp] >= prove[s][p] + public[d][pp] - 1 for each dependency (s depends on d)
    for s in 0..n {
        for dep in &input.deps.statement_deps[s].depends_on {
            if let StatementSource::Internal(d) = dep {
                for p in 1..max_pods {
                    for pp in 0..p {
                        // If s is proved in p and d is public in pp, then uses_input[p][pp] = 1
                        model = model.with(constraint!(
                            uses_input[p][pp] >= prove[s][p] + public[*d][pp] - 1.0
                        ));
                    }
                }
            }
        }
    }

    // Sum of uses_input for each POD <= max_input_pods
    for p in 1..max_pods {
        let input_sum: Expression = (0..p).map(|pp| uses_input[p][pp]).sum();
        model = model.with(constraint!(
            input_sum <= (input.params.max_input_pods as f64) * pod_used[p]
        ));
    }

    // Constraint 9: Symmetry breaking - use PODs in order
    // pod_used[p] >= pod_used[p+1]
    for p in 0..max_pods - 1 {
        model = model.with(constraint!(pod_used[p] >= pod_used[p + 1]));
    }

    // Solve
    let solution = model
        .solve()
        .map_err(|e| super::Error::Solver(format!("{:?}", e)))?;

    // Extract solution
    let mut pod_count = 0;
    for p in 0..max_pods {
        if solution.value(pod_used[p]) > 0.5 {
            pod_count = p + 1;
        }
    }

    let mut statement_to_pods: Vec<Vec<usize>> = vec![vec![]; n];
    let mut pod_statements: Vec<Vec<usize>> = vec![vec![]; pod_count];
    let mut pod_public_statements: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];

    for s in 0..n {
        for p in 0..pod_count {
            if solution.value(prove[s][p]) > 0.5 {
                statement_to_pods[s].push(p);
                pod_statements[p].push(s);
            }
            if solution.value(public[s][p]) > 0.5 {
                pod_public_statements[p].insert(s);
            }
        }
    }

    // POD 0 is the output POD (contains all user-requested public statements)
    let output_pod_indices = if input.output_public_indices.is_empty() {
        BTreeSet::new()
    } else {
        BTreeSet::from([0])
    };

    // Prove order is just 0..pod_count due to topological ordering constraint
    let prove_order: Vec<usize> = (0..pod_count).collect();

    Ok(MultiPodSolution {
        pod_count,
        statement_to_pods,
        pod_statements,
        pod_public_statements,
        prove_order,
        output_pod_indices,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::frontend::multi_pod::deps::StatementDeps;

    fn make_simple_deps(n: usize) -> DependencyGraph {
        DependencyGraph {
            statement_deps: (0..n)
                .map(|i| StatementDeps {
                    index: i,
                    depends_on: vec![],
                })
                .collect(),
            dependents: HashMap::new(),
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
        let output_public = BTreeSet::from([0, 1]);

        let input = SolverInput {
            num_statements: 5,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
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
        let output_public = BTreeSet::new();

        let input = SolverInput {
            num_statements: 6,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
        };

        let solution = solve(&input).unwrap();

        // 6 statements / 3 per pod = 2 PODs minimum
        assert!(solution.pod_count >= 2);
    }

    #[test]
    fn test_empty_input() {
        let params = Params::default();
        let costs: Vec<StatementCost> = vec![];
        let deps = make_simple_deps(0);
        let output_public = BTreeSet::new();

        let input = SolverInput {
            num_statements: 0,
            costs: &costs,
            deps: &deps,
            output_public_indices: &output_public,
            params: &params,
            max_pods: 20,
        };

        let solution = solve(&input).unwrap();
        assert_eq!(solution.pod_count, 0);
    }
}
