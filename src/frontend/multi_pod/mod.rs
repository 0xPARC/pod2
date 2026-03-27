//! Multi-POD builder for automatic statement packing.
//!
//! This module provides [`MultiPodBuilder`], a higher-level alternative to [`MainPodBuilder`]
//! that automatically handles cases where statements exceed per-POD resource limits by
//! splitting across multiple PODs.
//!
//! # Problem
//!
//! A single POD has resource limits (max statements, max custom predicate batches, etc.).
//! When a proof requires more resources than a single POD can provide, statements must
//! be split across multiple PODs with dependencies resolved via cross-POD copying.
//!
//! # Architecture
//!
//! The multi-POD system uses a recursive packing solver to find the minimal
//! assignment of statements to PODs. The solver works backwards from the
//! output pod's public statements, greedily packing each pod and recursing
//! on the residual. It minimizes the number of PODs while respecting:
//! - Per-POD resource limits (statements, batches, merkle proofs, etc.)
//! - Statement dependencies (if A depends on B, B must be available when proving A)
//! - Input POD limits (each POD can only reference a limited number of other PODs)
//!
//! # POD Ordering
//!
//! PODs are built in index order: 0, 1, 2, ..., k. The **output POD is always last**
//! (index k), containing the user-requested public statements. Earlier PODs (0..k-1)
//! are **intermediate PODs** that prove supporting statements.
//!
//! This ordering allows dependencies to flow forward: later PODs can access public
//! statements from earlier PODs by adding them as input PODs. The output POD, being
//! last, can access all intermediate PODs.
//!
//! # Usage
//!
//! ```ignore
//! let mut builder = MultiPodBuilder::new(&params, &vd_set);
//!
//! // Add operations (similar to MainPodBuilder)
//! let stmt_a = builder.priv_op(FrontendOp::eq(1, 1))?;
//! let stmt_b = builder.pub_op(FrontendOp::eq(2, 2))?;  // Will be public in output
//!
//! // Solve and prove
//! let result = builder.prove(&prover)?;
//!
//! // Access the output POD
//! let output = result.output_pod();
//! ```
//!
//! [`MainPodBuilder`]: crate::frontend::MainPodBuilder

use std::{
    collections::{BTreeSet, HashMap},
    fmt,
};

use crate::{
    frontend::{MainPod, MainPodBuilder, Operation},
    middleware::{Hash, MainPodProver, Params, Statement, VDSet, Value},
};

mod cost;
mod deps;
mod frontier_solver;
mod solution;

use cost::StatementCost;
use deps::{DependencyGraph, StatementSource};
pub use solution::MultiPodSolution;

/// Error type for multi-POD operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    Custom(String),
    /// Error from the frontend.
    Frontend(#[from] crate::frontend::Error),
    /// Error from the packing solver.
    Solver(String),
    /// No solution exists (shouldn't happen with valid input).
    NoSolution,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Custom(msg) => write!(f, "Custom error: {}", msg),
            Error::Frontend(e) => write!(f, "Frontend error: {}", e),
            Error::Solver(msg) => write!(f, "Solver error: {}", msg),
            Error::NoSolution => write!(f, "No solution exists"),
        }
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
    /// All PODs in build order (0, 1, ..., k).
    /// Intermediate PODs are at indices 0..k-1.
    /// The output POD is at index k (the last POD).
    pub pods: Vec<MainPod>,
}

impl MultiPodResult {
    /// Get the output POD (containing user-requested public statements).
    /// This is always the last POD (`pods[k]`), which can access all earlier
    /// intermediate PODs for dependencies.
    pub fn output_pod(&self) -> &MainPod {
        self.pods
            .last()
            .expect("MultiPodResult must have at least one POD")
    }

    /// Get intermediate/supporting PODs (all PODs except the output POD).
    /// These are at indices 0..k-1, built before the output POD.
    pub fn intermediate_pods(&self) -> &[MainPod] {
        &self.pods[..self.pods.len() - 1]
    }
}

/// Builder for creating multiple PODs when statements exceed per-POD limits.
///
/// # Overview
///
/// `MultiPodBuilder` provides a similar API to [`MainPodBuilder`], but automatically
/// splits statements across multiple PODs when resource limits are exceeded. The
/// workflow is:
///
/// 1. **Add operations**: Use [`priv_op`](Self::priv_op) and [`pub_op`](Self::pub_op)
///    to add statements, just like `MainPodBuilder`.
///
/// 2. **Solve**: Call [`solve`](Self::solve) to run the packing solver, which determines
///    the minimal assignment of statements to PODs. This consumes the builder and
///    returns a [`SolvedMultiPod`].
///
/// 3. **Prove**: Call [`prove`](SolvedMultiPod::prove) on the solved result to build
///    and prove all PODs.
///
/// # POD Structure
///
/// The result contains PODs in build order: intermediate PODs first (indices 0..k-1),
/// then the output POD last (index k). The output POD contains all user-requested
/// public statements (those added via `pub_op`). Intermediate PODs make their
/// statements public so later PODs can access them.
///
/// [`MainPodBuilder`]: crate::frontend::MainPodBuilder
#[derive(Debug)]
pub struct MultiPodBuilder {
    params: Params,
    vd_set: VDSet,
    options: Options,
    /// External input PODs (already proved).
    input_pods: Vec<MainPod>,
    /// Optional initial wildcard values for custom operations
    operations_wildcard_values: HashMap<usize, Vec<(usize, Value)>>,
    /// Indices of statements that should be public in output PODs.
    /// Uses Vec since max_public_statements is small (≤8); indices are naturally sorted.
    output_public_indices: Vec<usize>,
    /// Used during add_operation to validate statements with unlimited params.
    builder: MainPodBuilder,
}

/// A solved multi-POD problem, ready to be proved.
///
/// Created by [`MultiPodBuilder::solve`]. Call [`prove`](Self::prove) to build
/// and prove all PODs, or inspect the [`solution`](Self::solution) first.
#[derive(Debug)]
pub struct SolvedMultiPod {
    params: Params,
    vd_set: VDSet,
    input_pods: Vec<MainPod>,
    statements: Vec<Statement>,
    operations: Vec<Operation>,
    output_public_indices: Vec<usize>,
    operations_wildcard_values: HashMap<usize, Vec<(usize, Value)>>,
    solution: MultiPodSolution,
    deps: DependencyGraph,
}

impl SolvedMultiPod {
    /// Get the solver's solution (POD assignments).
    pub fn solution(&self) -> &MultiPodSolution {
        &self.solution
    }

    /// Build and prove all PODs.
    ///
    /// Builds PODs in dependency order (0, 1, ..., k) and proves each one.
    /// The last POD is the output POD containing user-requested public statements.
    pub fn prove(self, prover: &dyn MainPodProver) -> Result<MultiPodResult> {
        let solution = &self.solution;

        // Build PODs in sequential order: 0, 1, 2, ..., k
        // This order is guaranteed by the solver's symmetry-breaking constraint.
        // Later PODs may reference earlier ones for cross-POD dependencies.
        let mut pods: Vec<MainPod> = Vec::with_capacity(solution.pod_count);

        for pod_idx in 0..solution.pod_count {
            let pod = self.build_single_pod(pod_idx, &pods, prover)?;
            pods.push(pod);
        }

        Ok(MultiPodResult { pods })
    }

    /// Build a single POD based on the solver solution.
    ///
    /// This function translates the solver's abstract assignment into a concrete POD by:
    /// 1. Identifying which input PODs are needed (external + earlier generated)
    /// 2. Adding those input PODs to a fresh `MainPodBuilder`
    /// 3. For each statement assigned to this POD (in dependency order):
    ///    - Execute the original operation to create the statement
    ///    - Mark as public if the solver determined it should be
    /// 4. Prove the POD
    fn build_single_pod(
        &self,
        pod_idx: usize,
        earlier_pods: &[MainPod],
        prover: &dyn MainPodProver,
    ) -> Result<MainPod> {
        let mut builder = MainPodBuilder::new(&self.params, &self.vd_set);
        let solution = &self.solution;
        let statements_in_this_pod = &solution.pod_statements[pod_idx];

        // Step 1: Find which external and earlier PODs we need based on dependencies
        let (needed_earlier_pods, needed_external_pods) = self.compute_pod_inputs(pod_idx);

        // Step 2: Add input PODs to the builder
        for ext_idx in needed_external_pods {
            builder.add_pod(self.input_pods[ext_idx].clone())?;
        }
        for earlier_idx in needed_earlier_pods {
            builder.add_pod(earlier_pods[earlier_idx].clone())?;
        }

        // Step 3: Add statements in dependency order.
        // Statements are added in ascending index order, which matches dependency order:
        // if B depends on A, then A has a lower index and is added first.
        let statements_sorted: BTreeSet<usize> = statements_in_this_pod.iter().copied().collect();
        let public_set = &solution.pod_public_statements[pod_idx];

        for &stmt_idx in &statements_sorted {
            let op = self.operations[stmt_idx].clone();
            let wildcard_values = self
                .operations_wildcard_values
                .get(&stmt_idx)
                .cloned()
                .unwrap_or_default();

            let stmt = builder.op(false, wildcard_values, op)?;
            assert_eq!(stmt, self.statements[stmt_idx]); // Sanity check
        }

        // For the output pod, make statements public in the original order.
        // Intermediate pods use the solver-selected public set.
        if pod_idx == solution.pod_count - 1 {
            for idx in &self.output_public_indices {
                builder.reveal(&self.statements[*idx])?;
            }
        } else {
            for idx in public_set {
                builder.reveal(&self.statements[*idx])?;
            }
        }

        // Forward external premises only when the solver selected them as public
        // for this POD. These do not require local proving in this POD.
        for ext_premise_idx in &solution.pod_public_external_premises[pod_idx] {
            let ext_premise = &solution.external_premises[*ext_premise_idx];
            builder.reveal(&ext_premise.statement)?;
        }

        // Step 4: Prove the POD
        let pod = builder.prove(prover)?;

        Ok(pod)
    }

    /// Compute which input PODs (internal and external) are needed for a given POD.
    ///
    /// Returns (internal_pod_indices, external_pod_indices).
    fn compute_pod_inputs(&self, pod_idx: usize) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let solution = &self.solution;
        let internal_pods = solution.pod_internal_inputs[pod_idx].clone();
        let mut external_pods: BTreeSet<usize> = BTreeSet::new();

        for external_idx in &solution.pod_external_inputs[pod_idx] {
            let pod_hash = solution.external_pod_hashes[*external_idx];
            let idx = self
                .input_pods
                .iter()
                .position(|p| p.statements_hash() == pod_hash)
                .expect("external pod hash from solver solution");
            external_pods.insert(idx);
        }

        assert!(internal_pods.len() + external_pods.len() <= self.params.max_input_pods);

        (internal_pods, external_pods)
    }
}

impl fmt::Display for SolvedMultiPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let solution = &self.solution;
        let output_pod_idx = solution.pod_count.saturating_sub(1);

        // Header
        writeln!(
            f,
            "SolvedMultiPod: {} statements → {} PODs",
            self.statements.len(),
            solution.pod_count
        )?;

        if !self.input_pods.is_empty() {
            writeln!(f, "  External input PODs: {}", self.input_pods.len())?;
        }

        writeln!(f)?;

        // Per-POD breakdown
        for pod_idx in 0..solution.pod_count {
            let is_output = pod_idx == output_pod_idx;
            let role = if is_output { "output" } else { "intermediate" };

            writeln!(f, "  POD {} ({}):", pod_idx, role)?;

            // Show input PODs
            let (internal_inputs, external_inputs) = self.compute_pod_inputs(pod_idx);
            if !internal_inputs.is_empty() || !external_inputs.is_empty() {
                let internal_str: Vec<String> = internal_inputs
                    .iter()
                    .map(|i| format!("POD {}", i))
                    .collect();
                let external_str: Vec<String> = external_inputs
                    .iter()
                    .map(|i| format!("ext[{}]", i))
                    .collect();
                let all_inputs: Vec<&str> = internal_str
                    .iter()
                    .map(|s| s.as_str())
                    .chain(external_str.iter().map(|s| s.as_str()))
                    .collect();
                writeln!(
                    f,
                    "    inputs: {} (total: {})",
                    all_inputs.join(", "),
                    all_inputs.len()
                )?;
            }

            // Show statements
            let stmts = &solution.pod_statements[pod_idx];
            let public_stmts = &solution.pod_public_statements[pod_idx];

            for &stmt_idx in stmts {
                let stmt = &self.statements[stmt_idx];
                let is_public = public_stmts.contains(&stmt_idx);
                let visibility = if is_public { "public" } else { "private" };

                // Show dependencies for this statement
                let deps = &self.deps.statement_deps[stmt_idx];
                let dep_str = if deps.is_empty() {
                    String::new()
                } else {
                    let dep_parts: Vec<String> = deps
                        .iter()
                        .map(|d| match d {
                            StatementSource::Internal(i) => format!("stmt[{}]", i),
                            StatementSource::External(_) => "ext".to_string(),
                        })
                        .collect();
                    format!(" ← {}", dep_parts.join(", "))
                };

                writeln!(f, "    [{}] {} [{}]{}", stmt_idx, stmt, visibility, dep_str)?;
            }

            writeln!(f)?;
        }

        Ok(())
    }
}

impl MultiPodBuilder {
    /// Create a new MultiPodBuilder with default options.
    pub fn new(params: &Params, vd_set: &VDSet) -> Self {
        Self::new_with_options(params, vd_set, Options::default())
    }

    /// Create a new MultiPodBuilder with custom options.
    pub fn new_with_options(params: &Params, vd_set: &VDSet, options: Options) -> Self {
        let unlimited_params = Params {
            max_statements: usize::MAX / 2,
            max_public_statements: usize::MAX / 2,
            max_input_pods: usize::MAX / 2,
            max_input_pods_public_statements: usize::MAX / 2,
            ..params.clone()
        };
        let builder = MainPodBuilder::new(&unlimited_params, vd_set);
        Self {
            params: params.clone(),
            vd_set: vd_set.clone(),
            options,
            builder,
            input_pods: Vec::new(),
            operations_wildcard_values: HashMap::new(),
            output_public_indices: Vec::new(),
        }
    }

    /// Add an external input POD.
    pub fn add_pod(&mut self, pod: MainPod) -> Result<()> {
        self.builder.add_pod(pod.clone())?;
        self.input_pods.push(pod);
        Ok(())
    }

    /// Add a public operation (statement will be public in output).
    pub fn pub_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(true, vec![], op)
    }

    /// Add a private operation.
    pub fn priv_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(false, vec![], op)
    }

    // Find the index of a statement that has been added.  Panics if the statement doesn't
    // exist.
    fn stmt_index(&self, stmt: &Statement) -> usize {
        self.builder
            .statements
            .iter()
            .position(|s| s == stmt)
            .expect("exists")
    }

    pub fn op(
        &mut self,
        public: bool,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        let stmt = self.add_operation(wildcard_values, op)?;
        if public {
            let index = self.stmt_index(&stmt);
            if !self.output_public_indices.contains(&index) {
                self.output_public_indices.push(index);
            }
        }
        Ok(stmt)
    }

    /// Internal: Add an operation and create its statement.
    fn add_operation(
        &mut self,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        // Get or create the cached builder
        //
        // NOTE: We clone input pods here because MainPodBuilder takes ownership.
        // This could be avoided if MainPodBuilder were generic over the pod storage type:
        //   struct MainPodBuilder<P: Borrow<MainPod> = MainPod>
        // Then MultiPodBuilder could use MainPodBuilder<&MainPod> to borrow instead of clone,
        // while existing code using MainPodBuilder (with the default) would be unaffected.
        let stmt = self
            .builder
            .op(false, wildcard_values.clone(), op.clone())?;
        self.operations_wildcard_values
            .insert(self.stmt_index(&stmt), wildcard_values.clone());

        Ok(stmt)
    }

    /// Mark a statement as public in output.
    ///
    /// Returns an error if the statement was not found in the builder.
    /// Calling this multiple times on the same statement is idempotent.
    pub fn reveal(&mut self, stmt: &Statement) -> Result<()> {
        if let Some(idx) = self.builder.statements.iter().position(|s| s == stmt) {
            if !self.output_public_indices.contains(&idx) {
                self.output_public_indices.push(idx);
            }
            Ok(())
        } else {
            Err(Error::Custom(
                "reveal() called with statement not found in builder".to_string(),
            ))
        }
    }

    /// Get the number of statements.
    pub fn stmt_len(&self) -> usize {
        self.builder.stmt_len()
    }

    /// Solve the packing problem and return a solved builder ready for proving.
    ///
    /// This runs the packing solver to find the minimal POD assignment.
    /// Consumes the builder and returns a [`SolvedMultiPod`] that can be proved.
    pub fn solve(self) -> Result<SolvedMultiPod> {
        let MainPodBuilder {
            statements,
            operations,
            ..
        } = self.builder;
        // Compute costs for each statement
        let costs: Vec<StatementCost> = operations
            .iter()
            .map(StatementCost::from_operation)
            .collect();

        // Build external POD statement mapping
        let external_pod_statements = build_external_statement_map(&self.input_pods);

        // Build dependency graph
        let deps = DependencyGraph::build(&statements, &operations, &external_pod_statements);

        // Run solver
        let input = solution::SolverInput {
            costs: &costs,
            deps: &deps,
            output_public_indices: &self.output_public_indices,
            params: &self.params,
            max_pods: self.options.max_pods,
        };

        let solution = frontier_solver::solve(&input)?;

        Ok(SolvedMultiPod {
            params: self.params,
            vd_set: self.vd_set,
            input_pods: self.input_pods,
            statements,
            operations,
            output_public_indices: self.output_public_indices,
            operations_wildcard_values: self.operations_wildcard_values,
            solution,
            deps,
        })
    }
}

/// Build mapping from external POD statements to their POD hash.
fn build_external_statement_map(input_pods: &[MainPod]) -> HashMap<Statement, Hash> {
    let mut map = HashMap::new();
    for pod in input_pods {
        let pod_hash = pod.statements_hash();
        for stmt in pod.pod.pub_statements() {
            map.insert(stmt, pod_hash);
        }
    }
    map
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
        lang::load_module,
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
        let solved = builder.solve()?;
        assert_eq!(solved.solution().pod_count, 1);

        // Prove
        let prover = MockProver {};
        let result = solved.prove(&prover)?;

        assert_eq!(result.pods.len(), 1);
        assert!(result.intermediate_pods().is_empty());

        // Verify the POD
        result.pods[0].pod.verify().unwrap();

        Ok(())
    }

    #[test]
    fn test_duplicate_statement_content_reused_within_pod() -> Result<()> {
        // This test verifies that duplicate statement content is reused within a POD.
        // We run three operations, but each produces the same statement. This allows us to
        // deuplicate the private statement, matching the solver's deduplication logic.
        // Since there is only space for 2 private statements with these parameters, the
        // test can only succeed if deduplication is working correctly.
        // Public statements/reveals of private statements are not deduplicated, so we can
        // have 3 of them.
        let params = Params {
            max_statements: 5,
            max_public_statements: 3,
            // Derived: max_priv_statements = 2
            max_input_pods: 2,
            max_input_pods_public_statements: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.pub_op(FrontendOp::eq(7, 7))?;
        builder.pub_op(FrontendOp::eq(7, 7))?;
        builder.pub_op(FrontendOp::eq(7, 7))?;

        let solved = builder.solve()?;
        let pod_count = solved.solution().pod_count;

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        assert_eq!(result.pods.len(), pod_count);
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_cross_pod_dependencies() -> Result<()> {
        // Verifies that a dependency chain can be split across PODs.
        //
        // This tests the core multi-POD capability: when a dependency chain is too
        // long to fit in the output POD, intermediate statements must be proved in
        // earlier PODs and made public so the output POD can access them.
        //
        // Chain: b_out -> a_out -> contains
        //   - contains: base statement (dict_contains)
        //   - a_out: custom predicate taking contains as argument
        //   - b_out: custom predicate taking a_out as argument (OUTPUT-PUBLIC)
        //
        // With max_priv_statements = 2, we can't fit all 3 in one POD.
        // Expected solution:
        //   - POD 0 (intermediate): contains, a_out (with a_out public)
        //   - POD 1 (output): copy(a_out), b_out
        //
        // This requires intermediate PODs to feed INTO the output POD.

        // Tight params to force the dependency chain to be split.
        // With max_priv_statements = 2, we can't fit contains + a_out + b_out's
        // dependencies all in one POD.
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            // max_priv_statements = 2
            max_input_pods: 4,
            max_input_pods_public_statements: 20,
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // pred_a accepts a Contains statement
        // pred_b accepts a pred_a statement (Custom statement from pred_a)
        let module = load_module(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Statement 0: Contains (base of the chain)
        let dict = dict!({"k" => 1});
        let contains = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

        // Statement 1: Custom(pred_a), depends on contains
        let a_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_a").unwrap(),
            [contains],
        ))?;

        // Statement 2: Custom(pred_b), depends on a_out - make this output-public
        // This forces the dependency chain to be resolved for the output POD.
        let _b_out = builder.pub_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_b").unwrap(),
            [a_out],
        ))?;

        // Solve - this finds a multi-POD solution where intermediate PODs
        // provide dependencies to the output POD.
        let solved = builder.solve()?;
        let solution = solved.solution();

        // Expected: exactly 2 PODs
        //   Solution A:
        //   - POD 0 (intermediate): public statements 0 (contains)
        //   - POD 1 (output): inherits statement 0 (contains) from POD0, statement 1 (a_out),
        //   public statement 2 (b_out)
        //   Solution B:
        //   - POD 0 (intermediate): statements 0 (contains), public statement 1 (a_out)
        //   - POD 1 (output): inherits statement 1 (a_out) from POD0, public statement 2 (b_out)

        // Statement 2 (b_out) should be public in POD 1 (it's output-public)
        assert!(
            solution.pod_public_statements[1].contains(&2),
            "Statement 2 (b_out) should be public in output POD"
        );

        // Prove and verify all PODs
        let prover = MockProver {};
        let result = solved.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
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
    fn test_external_pods_routed_to_correct_parents() -> Result<()> {
        // Verifies that external input PODs are routed through the correct
        // parent pods when the output pod can't import them all directly.
        //
        // Two external PODs each provide a value. The output depends on
        // both via copies, but max_input_pods=2 means the output can fit
        // both external pods OR one external + one internal parent, not all
        // three. The solver must route one external through a parent.
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        let mut builder_a = MainPodBuilder::new(&params, vd_set);
        builder_a.pub_op(FrontendOp::eq(100, 100))?;
        let ext_pod_a = builder_a.prove(&prover)?;
        let stmt_a = ext_pod_a
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .unwrap();

        let mut builder_b = MainPodBuilder::new(&params, vd_set);
        builder_b.pub_op(FrontendOp::eq(200, 200))?;
        let ext_pod_b = builder_b.prove(&prover)?;
        let stmt_b = ext_pod_b
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .unwrap();

        let mut multi_builder = MultiPodBuilder::new(&params, vd_set);
        multi_builder.add_pod(ext_pod_a)?;
        multi_builder.add_pod(ext_pod_b)?;

        // Copy both external statements and make them public.
        // Also add a long custom pred chain so the output pod needs
        // internal parents too, forcing external pod routing.
        let copy_a = multi_builder.priv_op(FrontendOp::copy(stmt_a))?;
        let copy_b = multi_builder.priv_op(FrontendOp::copy(stmt_b))?;
        let last = add_custom_pred_chain(&mut multi_builder, 20, &params)?;
        multi_builder.pub_op(FrontendOp::copy(copy_a))?;
        multi_builder.pub_op(FrontendOp::copy(copy_b))?;
        multi_builder.pub_op(FrontendOp::copy(last))?;

        let solved = multi_builder.solve()?;
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs to route external deps, got {}",
            solved.solution().pod_count
        );

        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_private_statement_not_leaked_to_output_pod() -> Result<()> {
        // Verifies that private statements do not appear in the output POD's public slots.
        // The solver enforces that only user-requested public statements can be
        // public in the output POD (the last POD).

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

        let solved = builder.solve()?;
        let solution = solved.solution();

        // Check that the output POD's public statements are exactly the user-requested public ones.
        // The output POD is always the last one (index pod_count - 1).
        let output_pod_idx = solution.pod_count - 1;
        let output_public = &solution.pod_public_statements[output_pod_idx];
        assert!(
            output_public.contains(&3),
            "Public statement 3 should be public in output POD"
        );
        assert!(
            output_public.contains(&4),
            "Public statement 4 should be public in output POD"
        );

        // Private statements should NOT be public in output POD
        assert!(
            !output_public.contains(&0),
            "Private statement 0 should NOT be public in output POD"
        );
        assert!(
            !output_public.contains(&1),
            "Private statement 1 should NOT be public in output POD"
        );
        assert!(
            !output_public.contains(&2),
            "Private statement 2 should NOT be public in output POD"
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
        // Verifies that external input PODs are counted toward max_input_pods while
        // still allowing the solver to route external premises through intermediate PODs.
        //
        // Setup:
        // - max_input_pods = 2
        // - 3 external PODs (A, B, C), each with a public statement
        // - 3 public operations, each copying from a different external POD
        //
        // A direct 1-POD layout would need 3 external inputs in the output POD (infeasible),
        // so the solver should split the work and keep each generated POD within input limits.

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
        multi_builder.add_pod(ext_pod_a)?;
        multi_builder.add_pod(ext_pod_b)?;
        multi_builder.add_pod(ext_pod_c)?;

        // Add public operations that each depend on a different external POD.
        multi_builder.pub_op(FrontendOp::copy(stmt_a))?;
        multi_builder.pub_op(FrontendOp::copy(stmt_b))?;
        multi_builder.pub_op(FrontendOp::copy(stmt_c))?;

        // Solver should find a feasible multi-POD layout that respects input limits.
        let solved = multi_builder.solve()?;
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs to satisfy max_input_pods=2 with 3 external sources"
        );

        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_explicit_contains_not_double_counted_as_anchored_key() -> Result<()> {
        // Verifies that when a Contains statement is explicitly added and then used
        // as an anchored key argument, it's not double-counted in statement limits.
        //
        // Background: MainPodBuilder auto-inserts Contains statements for anchored keys
        // (dict, key pairs used as arguments to gt(), eq(), etc.). But if the Contains
        // was already explicitly added, no auto-insertion happens (PR 456).
        //
        // The solver must NOT count anchored key overhead when the producing Contains
        // statement is already in the same POD.
        //
        // Setup:
        // - max_priv_statements = 4
        // - Statement 0: dict_contains (public) - produces anchored key (dict, "x")
        // - Statements 1, 2, 3: gt(stmt_0, val) - each references the anchored key
        //
        // Correct counting for single POD:
        // - stmt_sum = 4 (statements 0-3)
        // - anchored_key_sum = 0 (statement 0 already provides the anchored key)
        // - Total = 4 ≤ max_priv_statements ✓
        //
        // Incorrect (double-counting) would give:
        // - stmt_sum = 4 + anchored_key_sum = 1 → Total = 5 > 4 ✗

        let params = Params {
            max_statements: 5,
            max_public_statements: 1, // max_priv_statements = 5 - 1 = 4
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Statement 0: public Contains - produces anchored key (dict, "x")
        let dict = dict!({"x" => 100});
        let contains_stmt = builder.pub_op(FrontendOp::dict_contains(dict, "x", 100))?;

        // Statements 1, 2, 3: each uses contains_stmt as an anchored key
        builder.priv_op(FrontendOp::gt(contains_stmt.clone(), 0))?;
        builder.priv_op(FrontendOp::gt(contains_stmt.clone(), 1))?;
        builder.priv_op(FrontendOp::gt(contains_stmt, 2))?;

        // With correct counting, all 4 statements fit in 1 POD
        let solved = builder.solve()?;
        assert_eq!(
            solved.solution().pod_count,
            1,
            "All statements should fit in 1 POD when Contains is not double-counted. \
             Got {} PODs, which suggests the explicit Contains is being incorrectly \
             counted as both a statement AND an anchored key overhead.",
            solved.solution().pod_count
        );

        // Verify proving works
        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        assert_eq!(result.pods.len(), 1);

        result.output_pod().pod.verify().unwrap();

        Ok(())
    }

    #[test]
    fn test_anchored_key_overhead_counted_in_statement_limit() -> Result<()> {
        // Verifies that anchored key overhead is correctly counted toward statement limits.
        //
        // When a Contains statement is used as an argument to operations like gt(),
        // it creates an "anchored key" reference. If the gt() is proved in a different
        // POD than the original Contains, MainPodBuilder auto-inserts a local Contains
        // statement for that anchored key. The solver must account for this overhead.
        //
        // Setup:
        // - max_priv_statements = 4 (small limit)
        // - Statement A: dict_contains (public, in POD 0)
        // - Statement B: eq (public, in POD 0)
        // - Statements C, D, E: gt(A, val) - each uses A as an anchored key
        //
        // The solver must account for the anchored key Contains statements that will
        // be auto-inserted when gt operations are proved in PODs other than POD 0.

        let params = Params {
            max_statements: 6,
            max_public_statements: 2, // max_priv_statements = 6 - 2 = 4
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Statement A: public Contains - proved in POD 0
        let dict = dict!({"x" => 100});
        let stmt_a = builder.pub_op(FrontendOp::dict_contains(dict, "x", 100))?;

        // Statement B: another public statement in POD 0
        builder.pub_op(FrontendOp::eq(200, 200))?;

        // Statements C, D, E: each uses stmt_a as an anchored key
        // When proved in a different POD, each needs a local Contains for the anchored key
        builder.priv_op(FrontendOp::gt(stmt_a.clone(), 0))?;
        builder.priv_op(FrontendOp::gt(stmt_a.clone(), 1))?;
        builder.priv_op(FrontendOp::gt(stmt_a, 2))?;

        let prover = MockProver {};
        let result = builder.solve()?.prove(&prover)?;

        // Verify all PODs
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_mixed_internal_and_external_pods_work_within_limit() -> Result<()> {
        // Verifies that scenarios with both internal and external dependencies work
        // when the total input count stays within max_input_pods.
        //
        // Setup:
        // - 1 external POD with a public statement
        // - 2 public dict_contains statements (uses anchored keys)
        // - 2 private gt statements that reference the dict_contains via anchored keys
        // - 1 private copy of the external POD's statement
        //
        // This tests that mixing internal POD dependencies (from earlier generated PODs)
        // and external POD dependencies (from user-provided input PODs) works correctly.

        let params = Params {
            max_statements: 10,
            max_public_statements: 3, // max_priv_statements = 7
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
        builder.add_pod(ext_pod)?;

        // Output POD: public Contains statements
        let dict0 = dict!({"x" => 100});
        let dict1 = dict!({"y" => 200});
        let contains_0 = builder.pub_op(FrontendOp::dict_contains(dict0, "x", 100))?;
        let contains_1 = builder.pub_op(FrontendOp::dict_contains(dict1, "y", 200))?;

        // Statements that depend on output POD
        builder.priv_op(FrontendOp::gt(contains_0, 0))?;
        builder.priv_op(FrontendOp::gt(contains_1, 0))?;

        // Depend on external POD
        builder.priv_op(FrontendOp::copy(stmt_ext))?;

        // This should succeed - total inputs per POD should stay within limit
        let result = builder.solve()?.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_long_dependency_chain_spans_multiple_pods() -> Result<()> {
        // Verifies that a long dependency chain correctly cascades through multiple
        // intermediate PODs before reaching the output POD.
        //
        // Chain: d_out -> c_out -> b_out -> a_out -> contains (5 statements)
        //
        // With max_priv_statements = 2, each POD can hold at most 2 statements.
        // Cross-POD dependencies are available via input PODs without needing copies.
        // Expected solution with 3 PODs (ceil(5/2) = 3):
        //   - POD 0 (intermediate): contains, a_out (a_out public for POD 1)
        //   - POD 1 (intermediate): b_out, c_out (c_out public for POD 2)
        //   - POD 2 (output): d_out (public)

        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            // max_priv_statements = 2
            max_input_pods: 4,
            max_input_pods_public_statements: 20,
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // Chain of predicates: each accepts the output of the previous
        let module = load_module(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            pred_c(X) = AND(pred_b(X))
            pred_d(X) = AND(pred_c(X))
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Build the chain: contains -> a_out -> b_out -> c_out -> d_out
        let dict = dict!({"k" => 1});
        let contains = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

        let a_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_a").unwrap(),
            [contains],
        ))?;

        let b_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_b").unwrap(),
            [a_out],
        ))?;

        let c_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_c").unwrap(),
            [b_out],
        ))?;

        let _d_out = builder.pub_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_d").unwrap(),
            [c_out],
        ))?;

        let solved = builder.solve()?;
        let solution = solved.solution();

        // Expected: exactly 3 PODs for a 5-statement chain with max_priv=2
        // (5 statements / 2 per POD = 3 PODs)
        assert_eq!(
            solution.pod_count, 3,
            "Expected exactly 3 PODs for 5-statement chain with max_priv=2"
        );

        // All 5 statements should be assigned across the PODs
        let all_statements: BTreeSet<usize> = solution
            .pod_statements
            .iter()
            .flat_map(|s| s.iter().copied())
            .collect();
        assert_eq!(
            all_statements,
            (0..5).collect::<BTreeSet<_>>(),
            "All 5 statements should be assigned"
        );

        // Each POD should have at most max_priv_statements = 2
        for (i, stmts) in solution.pod_statements.iter().enumerate() {
            assert!(
                stmts.len() <= 2,
                "POD {} has {} statements, but max_priv=2: {:?}",
                i,
                stmts.len(),
                stmts
            );
        }

        // The output POD (last) must contain d_out(4) and it must be public
        let output_pod_idx = solution.pod_count - 1;
        assert!(
            solution.pod_statements[output_pod_idx].contains(&4),
            "Output POD should contain statement 4 (d_out), got {:?}",
            solution.pod_statements[output_pod_idx]
        );
        assert!(
            solution.pod_public_statements[output_pod_idx].contains(&4),
            "Statement 4 (d_out) should be public in output POD"
        );

        // Prove and verify all PODs
        let prover = MockProver {};
        let result = solved.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_diamond_dependencies_across_pods() -> Result<()> {
        // Verifies that diamond-shaped dependencies work across PODs.
        //
        // Diamond structure:
        //           a_out (output)
        //          /      \
        //      b_out      c_out
        //          \      /
        //          contains
        //
        // Where a_out depends on BOTH b_out and c_out, creating a diamond.
        // The solver may distribute statements across PODs in various ways,
        // as long as dependencies are satisfied.

        let params = Params {
            max_statements: 6,
            max_public_statements: 3,
            // max_priv_statements = 3
            max_input_pods: 4,
            max_input_pods_public_statements: 20,
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        // pred_a takes TWO custom statement arguments (b_out and c_out)
        // pred_b and pred_c each take a Contains
        // Note: AND clauses are newline-separated, not comma-separated
        let module = load_module(
            r#"
            pred_b(X) = AND(Contains(X, "k", 1))
            pred_c(X) = AND(Contains(X, "k", 1))
            pred_a(X, Y) = AND(
                pred_b(X)
                pred_c(Y)
            )
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Base: single contains statement (shared by both branches conceptually,
        // but we need separate ones for pred_b and pred_c due to predicate signatures)
        let dict = dict!({"k" => 1});
        let contains = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

        // Left branch: b_out depends on contains
        let b_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_b").unwrap(),
            [contains.clone()],
        ))?;

        // Right branch: c_out depends on contains
        let c_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_c").unwrap(),
            [contains],
        ))?;

        // Top: a_out depends on BOTH b_out and c_out
        let _a_out = builder.pub_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_a").unwrap(),
            [b_out, c_out],
        ))?;

        let solved = builder.solve()?;
        let solution = solved.solution();

        // With 4 statements and max_priv=3, we need at least 2 PODs (ceil(4/3) = 2)
        assert_eq!(
            solution.pod_count, 2,
            "Expected exactly 2 PODs for diamond with max_priv=3"
        );

        // The output POD (last) must contain statement 3 (a_out) and it must be public
        let output_pod_idx = solution.pod_count - 1;
        assert!(
            solution.pod_statements[output_pod_idx].contains(&3),
            "Output POD should contain statement 3 (a_out), got {:?}",
            solution.pod_statements[output_pod_idx]
        );
        assert!(
            solution.pod_public_statements[output_pod_idx].contains(&3),
            "Statement 3 (a_out) should be public in output POD"
        );

        // All statements should be covered exactly once across all PODs
        let all_statements: BTreeSet<usize> = solution
            .pod_statements
            .iter()
            .flat_map(|s| s.iter().copied())
            .collect();
        assert_eq!(
            all_statements,
            [0, 1, 2, 3].into_iter().collect(),
            "All statements should be assigned to exactly one POD"
        );

        // Prove and verify all PODs - this validates dependencies are satisfied
        let prover = MockProver {};
        let result = solved.prove(&prover)?;

        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    /// Helper: populate a builder with n_dicts signed dicts x n_keys DictContains each.
    ///
    /// Each dict costs 1 SignedBy + n_keys merkle proofs. With default
    /// max_merkle_proofs_containers = 20, n_dicts x n_keys > 20 forces
    /// multiple PODs.
    /// Add a chain of `n` DictContains + equality checks with dependencies.
    ///
    /// Creates `n` dicts each containing `{"v" => 42}`, proves Contains on
    /// each, then chains them with equality comparisons:
    ///   contains_0 -> eq(contains_0, contains_1) -> eq(prev_eq, contains_2) -> ...
    ///
    /// Each Contains costs 1 merkle proof. The equality comparisons create
    /// dependencies between contains results, forcing the solver to respect
    /// ordering across pod boundaries. Returns the last statement.
    #[test]
    fn test_merkle_limit_forces_multi_pod() -> Result<()> {
        // A connected custom predicate chain where the root contains
        // check costs 1 merkle proof and each custom pred costs 1 cpv.
        // With a low merkle limit, a single contains still fits in one
        // pod, but the cpv chain forces multi-pod splitting. This tests
        // that the solver respects multiple resource dimensions and
        // maintains correct dependency routing across pods.
        //
        // 20 custom preds, max_cpv=4 -> ceil(20/4) = 5 pods minimum.
        let params = Params {
            max_custom_predicate_verifications: 4,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        let last = add_custom_pred_chain(&mut builder, 20, &params)?;
        builder.pub_op(FrontendOp::copy(last))?;

        let solved = builder.solve()?;
        let solution = solved.solution();

        assert!(
            solution.pod_count >= 5,
            "Expected at least 5 PODs for 20 cpv with limit 4, got {}",
            solution.pod_count
        );

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Frontier solver integration tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_frontier_single_pod() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        let mut signed_builder = SignedDictBuilder::new(&params);
        signed_builder.insert("value", 42);
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = signed_builder.sign(&signer).unwrap();

        builder.pub_op(FrontendOp::dict_signed_by(&signed_dict))?;

        let solved = builder.solve()?;
        assert_eq!(solved.solution().pod_count, 1);

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        result.pods[0].pod.verify().unwrap();

        Ok(())
    }

    #[test]
    fn test_frontier_overflow() -> Result<()> {
        // Force overflow via a dependency chain that exceeds per-pod capacity.
        // The frontier solver only proves statements
        // reachable from the output, so we need the private statements to
        // be in the output's dependency closure.
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            max_input_pods: 4,
            max_input_pods_public_statements: 20,
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let module = load_module(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            pred_c(X) = AND(pred_b(X))
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        let dict = dict!({"k" => 1});
        let contains = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;
        let a_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_a").unwrap(),
            [contains],
        ))?;
        let b_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_b").unwrap(),
            [a_out],
        ))?;
        let _c_out = builder.pub_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_c").unwrap(),
            [b_out],
        ))?;

        let solved = builder.solve()?;
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solved.solution().pod_count
        );

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_frontier_cross_pod_deps() -> Result<()> {
        // Same as test_cross_pod_dependencies but with frontier solver.
        let params = Params {
            max_statements: 4,
            max_public_statements: 2,
            max_input_pods: 4,
            max_input_pods_public_statements: 20,
            max_custom_predicate_verifications: 10,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let module = load_module(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        let dict = dict!({"k" => 1});
        let contains = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

        let a_out = builder.priv_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_a").unwrap(),
            [contains],
        ))?;

        let _b_out = builder.pub_op(FrontendOp::custom(
            batch.predicate_ref_by_name("pred_b").unwrap(),
            [a_out],
        ))?;

        let solved = builder.solve()?;
        let solution = solved.solution();
        assert!(
            solution.pod_count >= 1 && solution.pod_count <= 3,
            "Expected 1-3 PODs, got {}",
            solution.pod_count
        );

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    /// Build a chain of custom predicates that creates a true dependency chain.
    /// Each predicate wraps the previous one: pred_0(X) = Contains(X),
    /// pred_1(X) = pred_0(X), pred_2(X) = pred_1(X), etc.
    ///
    /// Returns (module, chain_length) for use in building the chain.
    fn build_chain_module(chain_len: usize, params: &Params) -> crate::lang::module::Module {
        let mut src = String::new();
        src.push_str("pred_0(X) = AND(Contains(X, \"k\", 1))\n");
        for i in 1..chain_len {
            src.push_str(&format!("pred_{}(X) = AND(pred_{}(X))\n", i, i - 1));
        }
        load_module(&src, "chain", params, &[]).expect("load chain module")
    }

    /// Helper: build a custom predicate chain of length `chain_len` on
    /// a builder, using default params. Returns the last statement.
    ///
    /// Produces chain_len + 1 statements (1 contains + chain_len custom preds),
    /// each depending on the previous. With default max_priv=40 and
    /// max_custom_predicate_verifications=8, a chain of 40 needs ~2 PODs
    /// from slot pressure, a chain of 80 needs ~3, etc.
    fn add_custom_pred_chain(
        builder: &mut MultiPodBuilder,
        chain_len: usize,
        params: &Params,
    ) -> Result<Statement> {
        let module = build_chain_module(chain_len, params);
        let batch = &module.batch;

        let dict = dict!({"k" => 1});
        let mut prev = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

        for i in 0..chain_len {
            let name = format!("pred_{}", i);
            prev = builder.priv_op(FrontendOp::custom(
                batch.predicate_ref_by_name(&name).unwrap(),
                [prev],
            ))?;
        }

        Ok(prev)
    }

    #[test]
    fn test_frontier_chain_default_params_k2() -> Result<()> {
        // Default params: max_priv=40, max_custom_pred_verifications=8.
        // Chain of 45 custom preds + 1 contains = 46 statements.
        // ceil(46/40) = 2 PODs from slot pressure. Also hits custom pred
        // verification limit (8 per pod) -> ceil(45/8) = 6 PODs.
        // The binding constraint is custom pred verifications.
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        let last = add_custom_pred_chain(&mut builder, 45, &params)?;
        builder.pub_op(FrontendOp::copy(last))?;

        let start = std::time::Instant::now();
        let solved = builder.solve()?;
        let elapsed = start.elapsed();
        let solution = solved.solution();

        eprintln!(
            "frontier default k2: pod_count={} time={:.1}ms",
            solution.pod_count,
            elapsed.as_secs_f64() * 1000.0
        );
        assert!(
            solution.pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solution.pod_count
        );

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_frontier_complex_multi_resource() -> Result<()> {
        // Complex scenario: two signed dicts (external PODs), contains checks,
        // two custom predicate branches that merge, cross-branch transitive_eq.
        //
        // Resource pressure from multiple dimensions:
        // - custom_pred_verifications (8/pod): 2 branches x 15 deep = 30 -> 4+ PODs
        // - statement slots (40/pod): ~50+ statements -> 2+ PODs
        // - input slots (2/pod): external pods + internal parents
        //
        // DAG structure (not linear):
        //   ext_a -> contains_a --\
        //                         +-- branch_a (15 custom preds) --\
        //   ext_b -> contains_b --/                                +-- merge -> output
        //                         +-- branch_b (15 custom preds) --/
        //   dict_c -> contains_c -/
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        // Create TWO external input PODs - this exercises external pod forwarding
        // since the output pod only has 2 input slots and needs internal parents too.
        let mut builder_ext_a = MainPodBuilder::new(&params, vd_set);
        builder_ext_a.pub_op(FrontendOp::eq(100, 100))?;
        let ext_pod_a = builder_ext_a.prove(&prover)?;
        let stmt_ext_a = ext_pod_a
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod_a public statement");

        let mut builder_ext_b = MainPodBuilder::new(&params, vd_set);
        builder_ext_b.pub_op(FrontendOp::eq(200, 200))?;
        let ext_pod_b = builder_ext_b.prove(&prover)?;
        let stmt_ext_b = ext_pod_b
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext_pod_b public statement");

        // Build custom predicate modules for two branches
        let branch_len = 15;
        let module_a = build_chain_module(branch_len, &params);
        let batch_a = &module_a.batch;
        let module_b = build_chain_module(branch_len, &params);
        let batch_b = &module_b.batch;

        // Build the multi-pod
        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Add both external pods
        builder.add_pod(ext_pod_a)?;
        builder.add_pod(ext_pod_b)?;
        let copy_ext_a = builder.priv_op(FrontendOp::copy(stmt_ext_a))?;
        let copy_ext_b = builder.priv_op(FrontendOp::copy(stmt_ext_b))?;

        // Layer 1: Two distinct dicts with Contains checks (merkle proof cost)
        let dict_c = dict!({"k" => 1, "id" => 1});
        let dict_d = dict!({"k" => 1, "id" => 2});
        let contains_c = builder.priv_op(FrontendOp::dict_contains(dict_c, "k", 1))?;
        let contains_d = builder.priv_op(FrontendOp::dict_contains(dict_d, "k", 1))?;

        // Layer 2: Branch A - chain of custom predicates rooted at contains_c
        let mut prev_a = contains_c;
        for i in 0..branch_len {
            let name = format!("pred_{}", i);
            prev_a = builder.priv_op(FrontendOp::custom(
                batch_a.predicate_ref_by_name(&name).unwrap(),
                [prev_a],
            ))?;
        }

        // Layer 2: Branch B - chain of custom predicates rooted at contains_d
        let mut prev_b = contains_d;
        for i in 0..branch_len {
            let name = format!("pred_{}", i);
            prev_b = builder.priv_op(FrontendOp::custom(
                batch_b.predicate_ref_by_name(&name).unwrap(),
                [prev_b],
            ))?;
        }

        // Layer 3: Both branches + both external references converge to output.
        // This forces the solver to route external pods through intermediates
        // since the output pod can't fit 2 external + 2 internal inputs.
        let _out_a = builder.pub_op(FrontendOp::copy(prev_a))?;
        let _out_b = builder.pub_op(FrontendOp::copy(prev_b))?;
        let _out_ext_a = builder.pub_op(FrontendOp::copy(copy_ext_a))?;
        let _out_ext_b = builder.pub_op(FrontendOp::copy(copy_ext_b))?;

        let start = std::time::Instant::now();
        let solved = builder.solve()?;
        let elapsed = start.elapsed();
        let solution = solved.solution();

        eprintln!(
            "frontier complex: pod_count={} time={:.1}ms statements={}",
            solution.pod_count,
            elapsed.as_secs_f64() * 1000.0,
            solution
                .pod_statements
                .iter()
                .map(|s| s.len())
                .sum::<usize>()
        );

        // With 30 custom pred verifications (limit 8/pod) -> at least 4 PODs.
        // Two independent branches means the solver must route both to the output.
        assert!(
            solution.pod_count >= 4,
            "Expected at least 4 PODs for 30 custom pred verifications (limit 8), got {}",
            solution.pod_count
        );

        // Prove and verify
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_frontier_complex_jumbo() -> Result<()> {
        // Jumbo test: 4 branches x 40 custom predicates = 160 verifications.
        // With limit 8/pod -> ceil(160/8) = 20 PODs minimum.
        // Each branch rooted at a distinct DictContains (merkle proof cost).
        // All branches converge to public outputs.
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        let n_branches = 4;
        let branch_len = 40;

        // Build one module per branch (each has 40 predicates)
        let modules: Vec<_> = (0..n_branches)
            .map(|_| build_chain_module(branch_len, &params))
            .collect();

        let mut builder = MultiPodBuilder::new(&params, vd_set);

        // Each branch: distinct dict -> contains -> 40-deep custom pred chain
        let mut branch_tips = Vec::new();
        for (branch_idx, module) in modules.iter().enumerate() {
            let batch = &module.batch;
            let dict = dict!({ "k" => 1, "branch" => branch_idx as i64 });
            let mut prev = builder.priv_op(FrontendOp::dict_contains(dict, "k", 1))?;

            for i in 0..branch_len {
                let name = format!("pred_{}", i);
                prev = builder.priv_op(FrontendOp::custom(
                    batch.predicate_ref_by_name(&name).unwrap(),
                    [prev],
                ))?;
            }
            branch_tips.push(prev);
        }

        // All branch tips converge to public outputs
        for tip in &branch_tips {
            builder.pub_op(FrontendOp::copy(tip.clone()))?;
        }

        let start = std::time::Instant::now();
        let solved = builder.solve()?;
        let elapsed = start.elapsed();
        let solution = solved.solution();

        eprintln!(
            "frontier jumbo: pod_count={} time={:.1}ms statements={}",
            solution.pod_count,
            elapsed.as_secs_f64() * 1000.0,
            solution
                .pod_statements
                .iter()
                .map(|s| s.len())
                .sum::<usize>()
        );

        assert!(
            solution.pod_count >= 20,
            "Expected at least 20 PODs for 160 custom pred verifications (limit 8), got {}",
            solution.pod_count
        );

        // Prove and verify all PODs
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }

    #[test]
    fn test_frontier_chain_default_params_k5() -> Result<()> {
        // Default params, chain of 100 custom preds.
        // ceil(100/8) = 13 PODs from custom pred verifications alone.
        // Tests that the frontier solver handles larger k quickly.
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        let last = add_custom_pred_chain(&mut builder, 100, &params)?;
        builder.pub_op(FrontendOp::copy(last))?;

        let start = std::time::Instant::now();
        let solved = builder.solve()?;
        let elapsed = start.elapsed();
        let solution = solved.solution();

        eprintln!(
            "frontier default k5+: pod_count={} time={:.1}ms",
            solution.pod_count,
            elapsed.as_secs_f64() * 1000.0
        );
        assert!(
            solution.pod_count >= 5,
            "Expected at least 5 PODs, got {}",
            solution.pod_count
        );

        let prover = MockProver {};
        let result = solved.prove(&prover)?;
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|_| panic!("POD {} verification failed", i));
        }

        Ok(())
    }
}
