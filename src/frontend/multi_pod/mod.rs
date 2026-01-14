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
    /// Cached dependency graph (computed once in solve(), reused in build_single_pod()).
    cached_deps: Option<DependencyGraph>,
    /// Cached external POD statement map (computed once in solve(), reused in build_single_pod()).
    cached_external_map: Option<HashMap<Statement, Hash>>,
    /// Cached MainPodBuilder for incremental statement computation.
    cached_builder: Option<MainPodBuilder>,
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
            cached_deps: None,
            cached_external_map: None,
            cached_builder: None,
        }
    }

    /// Add an external input POD.
    pub fn add_pod(&mut self, pod: MainPod) {
        // Keep cached_builder in sync if it exists
        if let Some(ref mut builder) = self.cached_builder {
            // Won't fail - cached_builder has unlimited params
            let _ = builder.add_pod(pod.clone());
        }
        self.input_pods.push(pod);
        self.invalidate_cache();
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
        self.invalidate_cache();

        // Get or create the cached builder
        //
        // NOTE: We clone input pods here because MainPodBuilder takes ownership.
        // This could be avoided if MainPodBuilder were generic over the pod storage type:
        //   struct MainPodBuilder<P: Borrow<MainPod> = MainPod>
        // Then MultiPodBuilder could use MainPodBuilder<&MainPod> to borrow instead of clone,
        // while existing code using MainPodBuilder (with the default) would be unaffected.
        let builder = self.cached_builder.get_or_insert_with(|| {
            let unlimited_params = Params {
                max_statements: usize::MAX / 2,
                max_public_statements: usize::MAX / 2,
                max_input_pods: usize::MAX / 2,
                max_input_pods_public_statements: usize::MAX / 2,
                ..self.params.clone()
            };
            let mut b = MainPodBuilder::new(&unlimited_params, &self.vd_set);
            for pod in &self.input_pods {
                let _ = b.add_pod(pod.clone());
            }
            b
        });

        let stmt = builder
            .op(false, vec![], op.clone())
            .map_err(|e| Error::Frontend(e.to_string()))?;

        self.statements.push(stmt.clone());
        self.operations.push(op);

        Ok(stmt)
    }

    /// Mark a statement as public in output.
    ///
    /// Returns an error if the statement was not found in the builder.
    /// Calling this multiple times on the same statement is idempotent.
    pub fn reveal(&mut self, stmt: &Statement) -> Result<()> {
        if let Some(idx) = self.statements.iter().position(|s| s == stmt) {
            // Only invalidate cache if this is a new reveal
            if self.output_public_indices.insert(idx) {
                self.invalidate_cache();
            }
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

    /// Invalidate all cached data. Called when operations or statements change.
    fn invalidate_cache(&mut self) {
        self.cached_solution = None;
        self.cached_deps = None;
        self.cached_external_map = None;
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

        // Build external POD statement mapping (cache for reuse in build_single_pod)
        let external_pod_statements = self.build_external_statement_map();
        self.cached_external_map = Some(external_pod_statements);
        let external_pod_statements = self.cached_external_map.as_ref().unwrap();

        // Build dependency graph (cache for reuse in build_single_pod)
        let deps =
            DependencyGraph::build(&self.statements, &self.operations, external_pod_statements);
        self.cached_deps = Some(deps);
        let deps = self.cached_deps.as_ref().unwrap();

        // Run solver
        let input = solver::SolverInput {
            num_statements: self.statements.len(),
            costs: &costs,
            deps,
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

        // Build PODs in prove_order. Due to symmetry breaking constraint (pod_used[p] >= pod_used[p+1]),
        // prove_order is always 0..pod_count, ensuring earlier PODs are built first.
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

        // Use cached dependency graph (computed in solve())
        let deps = self
            .cached_deps
            .as_ref()
            .expect("build_single_pod called before solve()");

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

        // Create a mapping from statement to its source (for copy operations).
        // A statement may be both proved locally AND available from an earlier POD.
        // We use or_insert to prefer local sources (inserted first) over earlier PODs.
        let mut stmt_sources: HashMap<usize, StmtSource> = HashMap::new();
        for &stmt_idx in statements_in_this_pod {
            stmt_sources.insert(stmt_idx, StmtSource::Local);
        }
        for earlier_pod_idx in 0..pod_idx {
            for &stmt_idx in &solution.pod_public_statements[earlier_pod_idx] {
                // Only insert if not already local - or_insert preserves existing entries
                stmt_sources.entry(stmt_idx).or_insert(StmtSource::FromPod);
            }
        }

        // Add statements in dependency order.
        // Note: Operations are already topologically ordered from how we construct them,
        // but the explicit sort is defensive and ensures correctness if that invariant changes.
        let topo_order = deps.topological_order();
        let statements_set: BTreeSet<usize> = statements_in_this_pod.iter().copied().collect();
        let public_set = &solution.pod_public_statements[pod_idx];

        // Track which statements have been added to this builder
        let mut added_statements: HashMap<usize, Statement> = HashMap::new();

        for &stmt_idx in &topo_order {
            if !statements_set.contains(&stmt_idx) {
                continue;
            }

            // First, ensure all dependencies are available (copy if needed).
            // When a dependency comes from an earlier POD, we need CopyStatement to make it
            // available in this POD's namespace. The earlier POD is already added as an input,
            // but CopyStatement creates a local reference that operations can use.
            for dep in &deps.statement_deps[stmt_idx].depends_on {
                if let StatementSource::Internal(dep_idx) = dep {
                    if !added_statements.contains_key(dep_idx) {
                        // Need to copy this statement from an earlier POD
                        match stmt_sources.get(dep_idx) {
                            Some(StmtSource::FromPod) => {
                                // Dependency is from an earlier POD - copy it
                                let copy_op = Operation(
                                    OperationType::Native(NativeOperation::CopyStatement),
                                    vec![OperationArg::Statement(
                                        self.statements[*dep_idx].clone(),
                                    )],
                                    OperationAux::None,
                                );
                                let copied_stmt = builder
                                    .priv_op(copy_op)
                                    .map_err(|e| Error::Frontend(e.to_string()))?;
                                added_statements.insert(*dep_idx, copied_stmt);
                            }
                            Some(StmtSource::Local) => {
                                // Local dependency should already be added due to topological
                                // ordering. If we reach here, there's a bug in the ordering.
                                unreachable!(
                                    "Local dependency at index {} should already be added \
                                     when processing statement {} (topological order violation)",
                                    dep_idx, stmt_idx
                                );
                            }
                            None => {
                                // Dependency not found in stmt_sources means it's neither
                                // in this POD nor available from earlier PODs - a solver bug.
                                unreachable!(
                                    "Dependency at index {} not found in stmt_sources \
                                     when processing statement {}",
                                    dep_idx, stmt_idx
                                );
                            }
                        }
                    }
                }
            }

            // Now add the actual statement
            let is_public = public_set.contains(&stmt_idx);
            let mut op = self.operations[stmt_idx].clone();

            // Remap Statement arguments in the operation to use statements created by MainPodBuilder.
            // The original operation references Statements from MultiPodBuilder, but MainPodBuilder
            // needs Statements that were either created by it or come from its input PODs.
            for arg in &mut op.1 {
                if let OperationArg::Statement(ref orig_stmt) = arg {
                    // Find the original statement's index in MultiPodBuilder
                    if let Some(orig_idx) = self.statements.iter().position(|s| s == orig_stmt) {
                        // Get the remapped statement from MainPodBuilder
                        if let Some(remapped_stmt) = added_statements.get(&orig_idx) {
                            *arg = OperationArg::Statement(remapped_stmt.clone());
                        }
                    }
                }
            }

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
    /// (The specific POD index doesn't matter - we only need to know it's not local.)
    FromPod,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::MockProver, primitives::ec::schnorr::SecretKey, signer::Signer,
        },
        dict,
        examples::MOCK_VD_SET,
        frontend::{Operation as FrontendOp, SignedDictBuilder},
        lang::parse,
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
        // Verifies that estimate_pod_count() provides a reasonable lower bound.
        let params = Params {
            max_statements: 10,
            max_public_statements: 5,
            // Derived: max_priv_statements = 10 - 5 = 5
            // With 5 statements, we need exactly 1 POD
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 5 public statements - all fit in one POD
        for i in 0..5 {
            builder.pub_op(FrontendOp::eq(i, i))?;
        }

        let estimate = builder.estimate_pod_count();
        let solution = builder.solve()?;

        // With 5 statements and capacity for 5, we need exactly 1 POD
        assert_eq!(solution.pod_count, 1, "5 statements should fit in 1 POD");

        // Estimate should be >= actual (lower bound with fudge factor)
        assert!(
            estimate >= solution.pod_count,
            "Estimate {} should be >= actual {}",
            estimate,
            solution.pod_count
        );

        Ok(())
    }

    #[test]
    fn test_multi_pod_overflow() -> Result<()> {
        // Verifies automatic splitting when statements exceed per-POD capacity.
        //
        // This test uses independent statements with no dependencies - the only
        // reason for multiple PODs is the statement limit being exceeded.
        let params = Params {
            max_statements: 6,
            max_public_statements: 2,
            // Derived: max_priv_statements = 6 - 2 = 4
            // With 6 private + 2 public = 8 statements, need ceil(8/4) = 2 PODs
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 6 independent private statements (no dependencies between them)
        for i in 0..6i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 2 public statements for the output POD
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;

        let pod_count = {
            let solution = builder.solve()?;
            // 8 statements / 4 per POD = 2 PODs minimum
            assert!(
                solution.pod_count >= 2,
                "Expected at least 2 PODs for 8 statements with max_priv=4, got {}",
                solution.pod_count
            );
            solution.pod_count
        };

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
    fn test_cross_pod_dependencies() -> Result<()> {
        // Verifies that dependencies work correctly when statements span POD boundaries.
        //
        // Each pair forms a dependency: lt(a, b) proves a < b, then lt_to_ne derives a ≠ b.
        // When statements are split across PODs, the solver must:
        // 1. Ensure dependencies are available (either proved locally or public in earlier POD)
        // 2. Insert CopyStatements to bring dependencies into the POD that needs them
        //
        // Setup: 8 statements with max_priv=4 forces splitting across 2+ PODs.
        let params = Params {
            max_statements: 6,
            max_public_statements: 2,
            // Derived: max_priv_statements = 6 - 2 = 4
            // With 8 statements, need ceil(8/4) = 2 PODs minimum
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Create 4 dependency pairs - enough to force cross-POD dependencies
        // Pair 1: prove balance < limit, derive balance ≠ limit
        let balance_under_limit = builder.priv_op(FrontendOp::lt(1, 100))?;
        let _balance_not_at_limit = builder.priv_op(FrontendOp::lt_to_ne(balance_under_limit))?;

        // Pair 2: prove age < max, derive age ≠ max
        let age_under_max = builder.priv_op(FrontendOp::lt(2, 200))?;
        let _age_not_at_max = builder.priv_op(FrontendOp::lt_to_ne(age_under_max))?;

        // Pair 3: prove score < threshold, derive score ≠ threshold
        let score_under_threshold = builder.priv_op(FrontendOp::lt(3, 300))?;
        let _score_not_at_threshold =
            builder.priv_op(FrontendOp::lt_to_ne(score_under_threshold))?;

        // Pair 4: prove level < cap, derive level ≠ cap (public output)
        let level_under_cap = builder.priv_op(FrontendOp::lt(4, 400))?;
        let _level_not_at_cap = builder.pub_op(FrontendOp::lt_to_ne(level_under_cap))?;

        let pod_count = {
            let solution = builder.solve()?;
            assert!(
                solution.pod_count >= 2,
                "Expected at least 2 PODs for 8 statements with max_priv=4, got {}",
                solution.pod_count
            );
            solution.pod_count
        };

        // Prove and verify all PODs
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
    fn test_isolated_pods_when_no_inputs_allowed() -> Result<()> {
        // Verifies that PODs are completely isolated when max_input_pods = 0.
        //
        // With no input PODs allowed, each generated POD must independently prove
        // all statements it contains - it cannot reference earlier PODs.
        // This is an edge case but validates the input POD constraint.
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            // Derived: max_priv_statements = 4 - 2 = 2
            max_input_pods: 0, // No input pods allowed - each POD is isolated
            max_input_pods_public_statements: 0,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add 4 independent private statements (no dependencies)
        // With max_priv=2, need 2 PODs. Since max_input_pods=0, they can't share.
        for i in 0..4i64 {
            builder.priv_op(FrontendOp::eq(i, i))?;
        }

        // Add 2 public statements for the output POD
        builder.pub_op(FrontendOp::eq(100, 100))?;
        builder.pub_op(FrontendOp::eq(101, 101))?;

        let solution = builder.solve()?;

        // 6 statements / 2 per POD = 3 PODs minimum
        assert!(
            solution.pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solution.pod_count
        );

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

    #[test]
    fn test_external_pods_counted_in_input_limit() -> Result<()> {
        // Verifies that external input PODs are counted toward max_input_pods.
        //
        // Setup:
        // - max_input_pods = 2
        // - 3 external PODs (A, B, C), each with a public statement
        // - 3 public operations, each copying from a different external POD
        //
        // Since all 3 must be public in POD 0 (the output POD), and POD 0 would need
        // all 3 external PODs as inputs (3 > max_input_pods), this is infeasible.
        // The solver should correctly detect and report this.

        let params = Params {
            max_statements: 10,
            max_public_statements: 5,
            max_input_pods: 2, // Only 2 input PODs allowed per generated POD
            max_input_pods_public_statements: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        // Create 3 external PODs, each with a distinct public statement
        let mut builder_a = MainPodBuilder::new(&params, vd_set);
        builder_a.pub_op(FrontendOp::eq(100, 100))?;
        let ext_pod_a = builder_a.prove(&prover)?;

        let mut builder_b = MainPodBuilder::new(&params, vd_set);
        builder_b.pub_op(FrontendOp::eq(200, 200))?;
        let ext_pod_b = builder_b.prove(&prover)?;

        let mut builder_c = MainPodBuilder::new(&params, vd_set);
        builder_c.pub_op(FrontendOp::eq(300, 300))?;
        let ext_pod_c = builder_c.prove(&prover)?;

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
        let stmt_c = ext_pod_c
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod_c should have a public statement");

        // Create MultiPodBuilder and add all 3 external PODs
        let mut multi_builder = MultiPodBuilder::new(&params, vd_set);
        multi_builder.add_pod(ext_pod_a);
        multi_builder.add_pod(ext_pod_b);
        multi_builder.add_pod(ext_pod_c);

        // Add public operations that each depend on a different external POD
        // All 3 must be public in POD 0, requiring 3 external inputs > max_input_pods
        multi_builder.pub_op(FrontendOp::copy(stmt_a))?;
        multi_builder.pub_op(FrontendOp::copy(stmt_b))?;
        multi_builder.pub_op(FrontendOp::copy(stmt_c))?;

        // Solver should correctly detect infeasibility and return an error
        let result = multi_builder.solve();
        assert!(
            result.is_err(),
            "Expected solver to report infeasibility, but got: {:?}",
            result
        );

        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("No feasible solution"),
            "Expected 'No feasible solution' error, got: {}",
            err_msg
        );

        Ok(())
    }

    #[test]
    fn test_copy_statements_counted_in_statement_limit() -> Result<()> {
        // Verifies that CopyStatements for cross-POD dependencies are counted
        // toward the statement limit.
        //
        // Setup:
        // - max_priv_statements = 2 (small limit)
        // - Statement A with no deps (public, goes to POD 0)
        // - Statements B, C, D all depend on A (private)
        //
        // Expected:
        // - Solver should recognize that if B, C, D go to POD 1, it needs a CopyStatement for A
        // - So POD 1 would have: CopyStatement(A) + B + C + D = 4 private statements
        // - This exceeds max_priv_statements = 2, so solver should create more PODs

        let params = Params {
            max_statements: 4,
            max_public_statements: 2, // max_priv_statements = 4 - 2 = 2
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Statement 0: public, no deps - will be in POD 0
        let stmt_a = builder.pub_op(FrontendOp::lt(1, 100))?;

        // Statements 1, 2, 3: private, all depend on statement 0
        // With max_priv_statements = 2, these can't all fit in POD 0
        // Solver must account for CopyStatement when distributing these
        builder.priv_op(FrontendOp::lt_to_ne(stmt_a.clone()))?;
        builder.priv_op(FrontendOp::lt_to_ne(stmt_a.clone()))?;
        builder.priv_op(FrontendOp::lt_to_ne(stmt_a))?;

        // Add another public statement for the output POD
        builder.pub_op(FrontendOp::eq(200, 200))?;

        // Solver should correctly account for CopyStatements and create enough PODs
        let prover = MockProver {};
        let result = builder.prove(&prover)?;

        // Verify all PODs
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_mixed_internal_and_external_pods_work_within_limit() -> Result<()> {
        // Verifies that scenarios with both internal and external dependencies work
        // when the total input count stays within max_input_pods.
        //
        // This is a sanity check that mixing internal and external POD dependencies
        // works correctly when limits are respected.

        let params = Params {
            max_statements: 6,
            max_public_statements: 3, // max_priv_statements = 3
            max_input_pods: 3,        // Allow up to 3 inputs per POD
            max_input_pods_public_statements: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        // Create 1 external POD
        let mut ext_builder = MainPodBuilder::new(&params, vd_set);
        ext_builder.pub_op(FrontendOp::eq(9999, 9999))?;
        let ext_pod = ext_builder.prove(&prover)?;

        let stmt_ext = ext_pod
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod should have a public statement");

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.add_pod(ext_pod);

        // Output POD: public statements
        let lt_0 = builder.pub_op(FrontendOp::lt(1, 100))?;
        let lt_1 = builder.pub_op(FrontendOp::lt(2, 200))?;

        // Statements that depend on output POD
        builder.priv_op(FrontendOp::lt_to_ne(lt_0))?;
        builder.priv_op(FrontendOp::lt_to_ne(lt_1))?;

        // Depend on external POD
        builder.priv_op(FrontendOp::copy(stmt_ext))?;

        // This should succeed - total inputs per POD should stay within limit
        let result = builder.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .map_err(|e| Error::Frontend(format!("POD {} verification failed: {}", i, e)))?;
        }

        Ok(())
    }

    #[test]
    fn test_signed_by_limit_forces_multi_pod() -> Result<()> {
        // Verifies that the solver respects max_signed_by per POD (C6f).
        //
        // Setup:
        // - max_signed_by = 2 (small limit)
        // - 4 SignedBy operations
        // - Other limits high enough not to interfere
        //
        // Expected: Solver creates exactly 2 PODs since 4 SignedBy / 2 per POD = 2 PODs
        let params = Params {
            max_statements: 48,
            max_public_statements: 8,
            // Derived: max_priv_statements = 48 - 8 = 40 (plenty of room)
            max_signed_by: 2, // Small limit to force splitting
            max_input_pods: 10,
            max_input_pods_public_statements: 20,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Create 4 different signed dicts
        for i in 0..4i64 {
            let mut signed_builder = SignedDictBuilder::new(&params);
            signed_builder.insert("id", i);
            let signer = Signer(SecretKey((i as u32 + 1).into()));
            let signed_dict = signed_builder.sign(&signer).unwrap();
            builder.priv_op(FrontendOp::dict_signed_by(&signed_dict))?;
        }

        // Add one public statement for output
        builder.pub_op(FrontendOp::eq(100, 100))?;

        let pod_count = {
            let solution = builder.solve()?;
            // 4 SignedBy / 2 per POD = exactly 2 PODs
            assert_eq!(
                solution.pod_count, 2,
                "Expected exactly 2 PODs for 4 SignedBy with max_signed_by=2, got {}",
                solution.pod_count
            );
            solution.pod_count
        };

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
    fn test_batch_cardinality_forces_multi_pod() -> Result<()> {
        // Verifies that the solver respects max_custom_predicate_batches per POD (C7).
        //
        // Setup:
        // - max_custom_predicate_batches = 2 (small limit)
        // - 4 different batches, each with one simple predicate
        // - 4 operations, one from each batch
        //
        // Expected: Solver creates exactly 2 PODs since 4 batches / 2 per POD = 2 PODs
        let params = Params {
            max_statements: 48,
            max_public_statements: 8,
            max_custom_predicate_batches: 2, // Small limit to force splitting
            max_input_pods: 10,
            max_input_pods_public_statements: 20,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // Create 4 separate batches using podlang parser
        // Each batch has a simple predicate that checks a Contains statement
        let batch1 = parse(r#"pred1(A) = AND(Contains(A, "x", 1))"#, &params, &[])
            .expect("parse batch1")
            .custom_batch;

        let batch2 = parse(r#"pred2(A) = AND(Contains(A, "x", 2))"#, &params, &[])
            .expect("parse batch2")
            .custom_batch;

        let batch3 = parse(r#"pred3(A) = AND(Contains(A, "x", 3))"#, &params, &[])
            .expect("parse batch3")
            .custom_batch;

        let batch4 = parse(r#"pred4(A) = AND(Contains(A, "x", 4))"#, &params, &[])
            .expect("parse batch4")
            .custom_batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add operations using predicates from each batch
        // Each custom predicate needs a Contains statement argument
        let dict1 = dict!({"x" => 1});
        let contains1 = builder.priv_op(FrontendOp::dict_contains(dict1, "x", 1))?;
        builder.priv_op(FrontendOp::custom(
            batch1.predicate_ref_by_name("pred1").unwrap(),
            [contains1],
        ))?;

        let dict2 = dict!({"x" => 2});
        let contains2 = builder.priv_op(FrontendOp::dict_contains(dict2, "x", 2))?;
        builder.priv_op(FrontendOp::custom(
            batch2.predicate_ref_by_name("pred2").unwrap(),
            [contains2],
        ))?;

        let dict3 = dict!({"x" => 3});
        let contains3 = builder.priv_op(FrontendOp::dict_contains(dict3, "x", 3))?;
        builder.priv_op(FrontendOp::custom(
            batch3.predicate_ref_by_name("pred3").unwrap(),
            [contains3],
        ))?;

        let dict4 = dict!({"x" => 4});
        let contains4 = builder.priv_op(FrontendOp::dict_contains(dict4, "x", 4))?;
        builder.pub_op(FrontendOp::custom(
            batch4.predicate_ref_by_name("pred4").unwrap(),
            [contains4],
        ))?;

        let pod_count = {
            let solution = builder.solve()?;
            // 4 batches / 2 per POD = exactly 2 PODs
            assert_eq!(
                solution.pod_count, 2,
                "Expected exactly 2 PODs for 4 batches with max_custom_predicate_batches=2, got {}",
                solution.pod_count
            );
            solution.pod_count
        };

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
}
