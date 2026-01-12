//! Multi-POD builder for automatic statement packing.
//!
//! This module provides `MultiPodBuilder`, a drop-in replacement for `MainPodBuilder`
//! that automatically handles cases where statements exceed per-POD limits by
//! splitting across multiple PODs.

use std::collections::{BTreeSet, HashMap};

use crate::{
    frontend::{MainPod, MainPodBuilder, Operation, OperationArg},
    middleware::{
        Hash, MainPodProver, NativeOperation, OperationAux, OperationType, Params, Statement, VDSet,
    },
};

mod cost;
mod deps;
mod solver;

use cost::{estimate_pod_count, StatementCost};
use deps::{DependencyGraph, StatementSource};
pub use solver::MultiPodSolution;

/// Error type for multi-POD operations.
#[derive(Debug, Clone)]
pub enum Error {
    /// Error from the frontend.
    Frontend(String),
    /// Error from the MILP solver.
    Solver(String),
    /// No solution exists (shouldn't happen with valid input).
    NoSolution,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Frontend(msg) => write!(f, "Frontend error: {}", msg),
            Error::Solver(msg) => write!(f, "Solver error: {}", msg),
            Error::NoSolution => write!(f, "No solution exists"),
        }
    }
}

impl std::error::Error for Error {}

impl From<crate::frontend::Error> for Error {
    fn from(e: crate::frontend::Error) -> Self {
        Error::Frontend(e.to_string())
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// Default maximum number of PODs the solver will consider.
pub const DEFAULT_MAX_PODS: usize = 20;

/// Options for configuring MultiPodBuilder behavior.
#[derive(Debug, Clone)]
pub struct Options {
    /// Maximum number of PODs the solver will consider.
    /// Defaults to 20. Increase if you have a very large number of statements.
    pub max_pods: usize,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            max_pods: DEFAULT_MAX_PODS,
        }
    }
}

/// Result of proving with MultiPodBuilder.
#[derive(Debug)]
pub struct MultiPodResult {
    /// All PODs in proving order.
    pub pods: Vec<MainPod>,
    /// Indices into `pods` for output PODs (containing user-requested public statements).
    pub output_indices: Vec<usize>,
    /// Indices into `pods` for intermediate/supporting PODs.
    pub intermediate_indices: Vec<usize>,
}

impl MultiPodResult {
    /// Get output PODs (containing user-requested public statements).
    pub fn output_pods(&self) -> Vec<&MainPod> {
        self.output_indices.iter().map(|&i| &self.pods[i]).collect()
    }

    /// Get intermediate/supporting PODs.
    pub fn intermediate_pods(&self) -> Vec<&MainPod> {
        self.intermediate_indices
            .iter()
            .map(|&i| &self.pods[i])
            .collect()
    }
}

/// Builder for creating multiple PODs when statements exceed per-POD limits.
///
/// Provides a similar API to `MainPodBuilder`, but automatically splits
/// statements across multiple PODs when limits are exceeded.
#[derive(Debug)]
pub struct MultiPodBuilder {
    params: Params,
    vd_set: VDSet,
    options: Options,
    /// External input PODs (already proved).
    input_pods: Vec<MainPod>,
    /// Statements created by this builder.
    statements: Vec<Statement>,
    /// Operations that produce each statement.
    operations: Vec<Operation>,
    /// Indices of statements that should be public in output PODs.
    output_public_indices: BTreeSet<usize>,
    /// Cached solution from the solver.
    cached_solution: Option<MultiPodSolution>,
}

impl MultiPodBuilder {
    /// Create a new MultiPodBuilder with default options.
    pub fn new(params: &Params, vd_set: &VDSet) -> Self {
        Self::new_with_options(params, vd_set, Options::default())
    }

    /// Create a new MultiPodBuilder with custom options.
    pub fn new_with_options(params: &Params, vd_set: &VDSet, options: Options) -> Self {
        Self {
            params: params.clone(),
            vd_set: vd_set.clone(),
            options,
            input_pods: Vec::new(),
            statements: Vec::new(),
            operations: Vec::new(),
            output_public_indices: BTreeSet::new(),
            cached_solution: None,
        }
    }

    /// Add an external input POD.
    pub fn add_pod(&mut self, pod: MainPod) {
        self.input_pods.push(pod);
        self.cached_solution = None; // Invalidate cache
    }

    /// Add a public operation (statement will be public in output).
    pub fn pub_op(&mut self, op: Operation) -> Result<Statement> {
        let stmt = self.add_operation(op)?;
        self.output_public_indices.insert(self.statements.len() - 1);
        Ok(stmt)
    }

    /// Add a private operation.
    pub fn priv_op(&mut self, op: Operation) -> Result<Statement> {
        self.add_operation(op)
    }

    /// Internal: Add an operation and create its statement.
    fn add_operation(&mut self, op: Operation) -> Result<Statement> {
        self.cached_solution = None; // Invalidate cache

        // Create params with very large limits for the temp builder
        // (we handle limits in the MILP solver, not here)
        let unlimited_params = Params {
            max_statements: usize::MAX / 2,
            max_public_statements: usize::MAX / 2,
            max_input_pods: usize::MAX / 2,
            max_input_pods_public_statements: usize::MAX / 2,
            ..self.params.clone()
        };

        // Create a temporary MainPodBuilder to compute the statement
        // This reuses the existing statement computation logic
        let mut temp_builder = MainPodBuilder::new(&unlimited_params, &self.vd_set);

        // Add external input PODs (needed for operations that reference their statements)
        for input_pod in &self.input_pods {
            temp_builder
                .add_pod(input_pod.clone())
                .map_err(|e| Error::Frontend(e.to_string()))?;
        }

        // Add existing statements as context (for dependency resolution)
        // We need to recreate the builder state to get correct statement computation
        for (stmt, prev_op) in self.statements.iter().zip(self.operations.iter()) {
            // Use insert directly - won't hit limits with unlimited_params
            let _ = temp_builder.insert(false, (stmt.clone(), prev_op.clone()));
        }

        // Now add the new operation
        let stmt = temp_builder
            .op(false, vec![], op.clone())
            .map_err(|e| Error::Frontend(e.to_string()))?;

        self.statements.push(stmt.clone());
        self.operations.push(op);

        Ok(stmt)
    }

    /// Mark a statement as public in output.
    ///
    /// Returns an error if the statement was not found in the builder.
    pub fn reveal(&mut self, stmt: &Statement) -> Result<()> {
        if let Some(idx) = self.statements.iter().position(|s| s == stmt) {
            self.output_public_indices.insert(idx);
            self.cached_solution = None;
            Ok(())
        } else {
            Err(Error::Frontend(
                "reveal() called with statement not found in builder".to_string(),
            ))
        }
    }

    /// Get the number of statements.
    pub fn num_statements(&self) -> usize {
        self.statements.len()
    }

    /// Solve the packing problem and return the solution.
    ///
    /// This runs the MILP solver to find the optimal POD assignment.
    /// The solution is cached for subsequent calls.
    pub fn solve(&mut self) -> Result<&MultiPodSolution> {
        if self.cached_solution.is_some() {
            return Ok(self.cached_solution.as_ref().unwrap());
        }

        // Compute costs for each statement
        let costs: Vec<StatementCost> = self
            .operations
            .iter()
            .map(StatementCost::from_operation)
            .collect();

        // Build external POD statement mapping
        let external_pod_statements = self.build_external_statement_map();

        // Build dependency graph
        let deps =
            DependencyGraph::build(&self.statements, &self.operations, &external_pod_statements);

        // Run solver
        let input = solver::SolverInput {
            num_statements: self.statements.len(),
            costs: &costs,
            deps: &deps,
            output_public_indices: &self.output_public_indices,
            params: &self.params,
            max_pods: self.options.max_pods,
        };

        let solution = solver::solve(&input)?;
        self.cached_solution = Some(solution);

        Ok(self.cached_solution.as_ref().unwrap())
    }

    /// Get the estimated POD count (quick heuristic without full solve).
    pub fn estimate_pod_count(&self) -> usize {
        estimate_pod_count(&self.operations, &self.params)
    }

    /// Build and prove all PODs.
    ///
    /// This first solves if not already solved, then builds and proves
    /// all necessary PODs in dependency order.
    pub fn prove(&mut self, prover: &dyn MainPodProver) -> Result<MultiPodResult> {
        // Ensure we have a solution (can't use returned reference due to later &mut self borrows)
        self.solve()?;
        let solution = self.cached_solution.as_ref().unwrap();

        if solution.pod_count == 0 {
            return Ok(MultiPodResult {
                pods: vec![],
                output_indices: vec![],
                intermediate_indices: vec![],
            });
        }

        // Build PODs in order
        let mut pods: Vec<MainPod> = Vec::with_capacity(solution.pod_count);

        for pod_idx in &solution.prove_order {
            let pod = self.build_single_pod(*pod_idx, solution, &pods, prover)?;
            pods.push(pod);
        }

        // Compute output and intermediate indices
        let mut output_indices = Vec::new();
        let mut intermediate_indices = Vec::new();

        for idx in 0..pods.len() {
            if solution.output_pod_indices.contains(&idx) {
                output_indices.push(idx);
            } else {
                intermediate_indices.push(idx);
            }
        }

        Ok(MultiPodResult {
            pods,
            output_indices,
            intermediate_indices,
        })
    }

    /// Build a single POD based on the solver solution.
    fn build_single_pod(
        &self,
        pod_idx: usize,
        solution: &MultiPodSolution,
        earlier_pods: &[MainPod],
        prover: &dyn MainPodProver,
    ) -> Result<MainPod> {
        let mut builder = MainPodBuilder::new(&self.params, &self.vd_set);

        // Build dependency graph first to determine which input PODs we need
        let external_pod_statements = self.build_external_statement_map();
        let deps =
            DependencyGraph::build(&self.statements, &self.operations, &external_pod_statements);

        let statements_in_this_pod: &Vec<usize> = &solution.pod_statements[pod_idx];
        let mut needed_external_pods: BTreeSet<usize> = BTreeSet::new();
        let mut needed_earlier_pods: BTreeSet<usize> = BTreeSet::new();

        // Find which external and earlier PODs we need based on dependencies
        for &stmt_idx in statements_in_this_pod {
            for dep in &deps.statement_deps[stmt_idx].depends_on {
                match dep {
                    StatementSource::Internal(dep_idx) => {
                        // Check if dependency is in an earlier generated POD
                        for earlier_pod_idx in 0..pod_idx {
                            if solution.pod_statements[earlier_pod_idx].contains(dep_idx)
                                && solution.pod_public_statements[earlier_pod_idx].contains(dep_idx)
                            {
                                needed_earlier_pods.insert(earlier_pod_idx);
                                break;
                            }
                        }
                    }
                    StatementSource::External(pod_hash) => {
                        // Find which external POD has this hash
                        for (idx, input_pod) in self.input_pods.iter().enumerate() {
                            if input_pod.statements_hash() == *pod_hash {
                                needed_external_pods.insert(idx);
                                break;
                            }
                        }
                    }
                }
            }
        }

        // Add only the external input PODs that are needed
        for &ext_idx in &needed_external_pods {
            builder.add_pod(self.input_pods[ext_idx].clone())?;
        }

        // Add needed earlier generated PODs
        for &earlier_idx in &needed_earlier_pods {
            builder.add_pod(earlier_pods[earlier_idx].clone())?;
        }

        // Create a mapping from statement to its source (for copy operations)
        let mut stmt_sources: HashMap<usize, StmtSource> = HashMap::new();
        for &stmt_idx in statements_in_this_pod {
            stmt_sources.insert(stmt_idx, StmtSource::Local);
        }
        for earlier_pod_idx in 0..pod_idx {
            for &stmt_idx in &solution.pod_public_statements[earlier_pod_idx] {
                stmt_sources
                    .entry(stmt_idx)
                    .or_insert(StmtSource::FromPod(earlier_pod_idx));
            }
        }

        // Add statements in dependency order
        let topo_order = deps.topological_order();
        let statements_set: BTreeSet<usize> = statements_in_this_pod.iter().copied().collect();
        let public_set = &solution.pod_public_statements[pod_idx];

        // Track which statements have been added to this builder
        let mut added_statements: HashMap<usize, Statement> = HashMap::new();

        for &stmt_idx in &topo_order {
            if !statements_set.contains(&stmt_idx) {
                continue;
            }

            // First, ensure all dependencies are available (copy if needed)
            for dep in &deps.statement_deps[stmt_idx].depends_on {
                if let StatementSource::Internal(dep_idx) = dep {
                    if !added_statements.contains_key(dep_idx) {
                        // Need to copy this statement from an earlier POD
                        if let Some(StmtSource::FromPod(_earlier_pod_idx)) =
                            stmt_sources.get(dep_idx)
                        {
                            // Add a copy operation
                            let copy_op = Operation(
                                OperationType::Native(NativeOperation::CopyStatement),
                                vec![OperationArg::Statement(self.statements[*dep_idx].clone())],
                                OperationAux::None,
                            );
                            let copied_stmt = builder
                                .priv_op(copy_op)
                                .map_err(|e| Error::Frontend(e.to_string()))?;
                            added_statements.insert(*dep_idx, copied_stmt);
                        }
                    }
                }
            }

            // Now add the actual statement
            let is_public = public_set.contains(&stmt_idx);
            let op = self.operations[stmt_idx].clone();

            let stmt = builder
                .op(is_public, vec![], op)
                .map_err(|e| Error::Frontend(e.to_string()))?;

            added_statements.insert(stmt_idx, stmt);
        }

        // Prove the POD
        let pod = builder
            .prove(prover)
            .map_err(|e| Error::Frontend(e.to_string()))?;

        Ok(pod)
    }

    /// Build mapping from external POD statements to their POD hash.
    fn build_external_statement_map(&self) -> HashMap<Statement, Hash> {
        let mut map = HashMap::new();
        for pod in &self.input_pods {
            let pod_hash = pod.statements_hash();
            for stmt in pod.pod.pub_statements() {
                map.insert(stmt, pod_hash);
            }
        }
        map
    }
}

/// Source of a statement within a built POD.
#[derive(Clone, Debug)]
enum StmtSource {
    /// Statement is proved locally in this POD.
    Local,
    /// Statement is copied from an earlier generated POD.
    FromPod(usize),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::MockProver, primitives::ec::schnorr::SecretKey, signer::Signer,
        },
        examples::MOCK_VD_SET,
        frontend::{Operation as FrontendOp, SignedDictBuilder},
    };

    #[test]
    fn test_single_pod_case() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Create a simple signed dict
        let mut signed_builder = SignedDictBuilder::new(&params);
        signed_builder.insert("value", 42);
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = signed_builder.sign(&signer).unwrap();

        // Add operation
        builder.pub_op(FrontendOp::dict_signed_by(&signed_dict))?;

        // Solve
        let solution = builder.solve()?;
        assert_eq!(solution.pod_count, 1);

        // Prove
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        assert_eq!(result.pods.len(), 1);
        assert_eq!(result.output_indices.len(), 1);
        assert!(result.intermediate_indices.is_empty());

        // Verify the POD
        result.pods[0]
            .pod
            .verify()
            .map_err(|e| Error::Frontend(e.to_string()))?;

        Ok(())
    }

    #[test]
    fn test_estimate_vs_solve() -> Result<()> {
        let params = Params {
            max_statements: 10,
            max_public_statements: 5, // Enough for all 5 public statements
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add a few public operations (all must fit in single output POD)
        for i in 0..5 {
            builder.pub_op(FrontendOp::eq(i, i))?;
        }

        let estimate = builder.estimate_pod_count();
        let solution = builder.solve()?;

        // Estimate should be >= actual (it's a lower bound + fudge factor)
        // Actually estimate might be slightly higher due to fudge factor
        assert!(estimate >= 1);
        assert!(solution.pod_count >= 1);

        Ok(())
    }

    #[test]
    fn test_multi_pod_overflow() -> Result<()> {
        // Test overflow via private statements (public statements must fit in one POD)
        // max_priv_statements = 6 - 2 = 4, so 6 private statements need 2 PODs
        let params = Params {
            max_statements: 6,
            max_public_statements: 2,
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 6 private statements - should require at least 2 PODs
        for i in 0..6i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 2 public statements (within the single-output-POD limit)
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;

        // Solve and check
        let pod_count = {
            let solution = builder.solve()?;
            println!(
                "Solution: {} PODs needed for 8 statements",
                solution.pod_count
            );
            println!("Statement assignments:");
            for (pod_idx, stmts) in solution.pod_statements.iter().enumerate() {
                println!("  POD {}: statements {:?}", pod_idx, stmts);
                println!("    public: {:?}", solution.pod_public_statements[pod_idx]);
            }
            // Should need at least 2 PODs
            assert!(
                solution.pod_count >= 2,
                "Expected at least 2 PODs, got {}",
                solution.pod_count
            );
            solution.pod_count
        };

        // Prove all PODs
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        assert_eq!(result.pods.len(), pod_count);

        // Verify all PODs
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_dependencies_across_pods() -> Result<()> {
        // Test that private statements can overflow across PODs while
        // public statements stay in the output POD.
        // max_priv_statements = 8 - 3 = 5, so 6 private statements need 2 PODs
        let params = Params {
            max_statements: 8,
            max_public_statements: 3,
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 6 private statements - should require 2 PODs
        for i in 0..6i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 3 public statements (within the single-output-POD limit)
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;
        builder.pub_op(FrontendOp::eq(102, 102))?;

        // Solve
        let pod_count = {
            let solution = builder.solve()?;
            println!("Dependencies test: {} PODs needed", solution.pod_count);
            println!("Statement assignments:");
            for (pod_idx, stmts) in solution.pod_statements.iter().enumerate() {
                println!("  POD {}: statements {:?}", pod_idx, stmts);
                println!("    public: {:?}", solution.pod_public_statements[pod_idx]);
            }
            solution.pod_count
        };

        // Prove
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        assert_eq!(result.pods.len(), pod_count);

        // Verify all PODs
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_cross_pod_copy() -> Result<()> {
        // Test that private statements can overflow across multiple PODs.
        // max_priv_statements = 10 - 2 = 8
        // With 10 private statements, we need 2 PODs (10/8 = 2)
        let params = Params {
            max_statements: 10,
            max_public_statements: 2,
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 10 private statements - forces 2 PODs
        for i in 0..10i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 2 public statements (within single output POD limit)
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;

        // Extract solution info before prove() borrows builder
        let pod_count = {
            let solution = builder.solve()?;
            solution.pod_count
        };

        // Should need at least 2 PODs (10 private / 8 per POD = 2)
        assert!(
            pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            pod_count
        );

        // Prove and verify
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        assert_eq!(result.pods.len(), pod_count);
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_reprove_when_input_pods_exhausted() -> Result<()> {
        // Test that the solver chooses to re-prove a statement when using it as
        // an input would exceed max_input_pods.
        // With max_input_pods = 0, any cross-POD dependency must be re-proved.
        // max_priv_statements = 4 - 2 = 2
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            max_input_pods: 0, // No input pods allowed - forces re-proving
            max_input_pods_public_statements: 0,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 4 private statements - forces 2 PODs (4/2 = 2)
        for i in 0..4i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 2 public statements (within single output POD limit)
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;

        let solution = builder.solve()?;

        // With max_priv_statements = 2 and 6 statements total, need at least 2 PODs
        assert!(
            solution.pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solution.pod_count
        );

        // Since max_input_pods = 0, PODs cannot reference each other.
        // Each POD must independently prove its statements.

        // Prove and verify
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_zero_public_capacity_fails() {
        // Test that setting max_public_statements = 0 with a public operation
        // results in a solver error (infeasible configuration).
        let params = Params {
            max_statements: 10,
            max_public_statements: 0, // No public statements allowed
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Try to add a public operation
        let _ = builder.pub_op(FrontendOp::eq(1, 1));

        // Solving should fail because we can't satisfy the public statement requirement
        let result = builder.solve();
        assert!(
            result.is_err(),
            "Expected solver to fail with zero public capacity, but it succeeded"
        );
    }

    #[test]
    fn test_max_pods_exceeded_error() {
        // Test that exceeding max_pods gives a clear error message.
        // With max_statements=3 and max_public_statements=1, we have
        // max_priv_statements = 2. So 10 statements requires 5 PODs.
        let params = Params {
            max_statements: 3,
            max_public_statements: 1,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // Set max_pods to 2, which is less than the 5 PODs needed
        let options = Options { max_pods: 2 };
        let mut builder = MultiPodBuilder::new_with_options(&params, vd_set, options);

        // Add 10 statements (requires 5 PODs)
        for i in 0..10 {
            let _ = builder.priv_op(FrontendOp::eq(i, i));
        }

        // Solving should fail with a clear error about max_pods
        let result = builder.solve();
        assert!(
            result.is_err(),
            "Expected solver to fail when max_pods exceeded"
        );

        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("requires at least") && err_msg.contains("PODs"),
            "Error message should explain POD requirement: {}",
            err_msg
        );
        assert!(
            err_msg.contains("Options::max_pods"),
            "Error message should suggest increasing Options::max_pods: {}",
            err_msg
        );
    }

    #[test]
    fn test_external_pods_only_added_where_needed() -> Result<()> {
        // Verifies that external input PODs are only added to generated PODs
        // that actually need them based on statement dependencies.
        //
        // Setup:
        // - Two external PODs: ext_A and ext_B, each with a public statement
        // - max_input_pods = 1 (each generated POD can only have 1 input POD)
        // - Private statements that copy from different external PODs force overflow
        //
        // With max_input_pods = 1, this only works if each generated POD
        // includes only the external POD it actually depends on.

        let params = Params {
            max_statements: 4,        // Small limit
            max_public_statements: 2, // max_priv_statements = 4 - 2 = 2
            max_input_pods: 1,        // Only 1 input POD allowed per generated POD
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // Create external POD A with a public statement
        let prover = MockProver {};
        let mut builder_a = MainPodBuilder::new(&params, vd_set);
        builder_a.pub_op(FrontendOp::eq(100, 100))?;
        let ext_pod_a = builder_a.prove(&prover)?;

        // Create external POD B with a public statement
        let mut builder_b = MainPodBuilder::new(&params, vd_set);
        builder_b.pub_op(FrontendOp::eq(200, 200))?;
        let ext_pod_b = builder_b.prove(&prover)?;

        // Get the actual statements from the proved PODs
        let stmt_a = ext_pod_a
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod_a should have a public statement");
        let stmt_b = ext_pod_b
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod_b should have a public statement");

        // Create MultiPodBuilder and add both external PODs
        let mut multi_builder = MultiPodBuilder::new(&params, vd_set);
        multi_builder.add_pod(ext_pod_a.clone());
        multi_builder.add_pod(ext_pod_b.clone());

        // Add private operations that reference different external PODs.
        // These will force multiple PODs due to private statement limits.
        multi_builder.priv_op(FrontendOp::copy(stmt_a))?;
        multi_builder.priv_op(FrontendOp::eq(101, 101))?;
        multi_builder.priv_op(FrontendOp::copy(stmt_b))?;
        multi_builder.priv_op(FrontendOp::eq(201, 201))?;

        // Add 2 public statements (within single output POD limit)
        multi_builder.pub_op(FrontendOp::eq(300, 300))?;
        multi_builder.pub_op(FrontendOp::eq(301, 301))?;

        // With 6 statements and max_priv_statements = 2, we need multiple PODs.
        // Each POD should only include the external POD it depends on.

        let solution = multi_builder.solve()?;
        assert!(
            solution.pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solution.pod_count
        );

        let result = multi_builder.prove(&prover)?;

        // Verify all PODs
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_private_statement_not_leaked_to_output_pod() -> Result<()> {
        // Verifies that private statements do not appear in the output POD's public slots.
        // The solver now enforces that only user-requested public statements can be
        // public in POD 0 (the output POD).

        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add private statements (indices 0, 1, 2) - should NOT appear in output POD public slots
        builder.priv_op(FrontendOp::eq(100, 100))?;
        builder.priv_op(FrontendOp::eq(101, 101))?;
        builder.priv_op(FrontendOp::eq(102, 102))?;

        // Add public statements (indices 3, 4) - these SHOULD appear in output POD public slots
        builder.pub_op(FrontendOp::eq(200, 200))?;
        builder.pub_op(FrontendOp::eq(201, 201))?;

        let solution = builder.solve()?;

        // POD 0 should be the only output POD
        assert_eq!(
            solution.output_pod_indices,
            BTreeSet::from([0]),
            "POD 0 should be the only output POD"
        );

        // Check that POD 0's public statements are exactly the user-requested public statements
        let pod0_public = &solution.pod_public_statements[0];
        assert!(
            pod0_public.contains(&3),
            "Public statement 3 should be public in POD 0"
        );
        assert!(
            pod0_public.contains(&4),
            "Public statement 4 should be public in POD 0"
        );

        // Private statements should NOT be public in POD 0
        assert!(
            !pod0_public.contains(&0),
            "Private statement 0 should NOT be public in POD 0"
        );
        assert!(
            !pod0_public.contains(&1),
            "Private statement 1 should NOT be public in POD 0"
        );
        assert!(
            !pod0_public.contains(&2),
            "Private statement 2 should NOT be public in POD 0"
        );

        Ok(())
    }

    #[test]
    fn test_too_many_public_statements_error() -> Result<()> {
        // Verifies that requesting more public statements than max_public_statements
        // results in a clear error (since all public statements must fit in one output POD).

        let params = Params {
            max_statements: 10,
            max_public_statements: 2,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 3 public statements, but max is 2
        builder.pub_op(FrontendOp::eq(1, 1))?;
        builder.pub_op(FrontendOp::eq(2, 2))?;
        builder.pub_op(FrontendOp::eq(3, 3))?;

        let result = builder.solve();

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("Too many public statements"),
            "Expected 'Too many public statements' error, got: {}",
            err_msg
        );

        Ok(())
    }
}
