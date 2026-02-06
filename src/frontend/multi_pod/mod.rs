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
//! The multi-POD system uses a MILP (Mixed Integer Linear Program) solver to find the
//! optimal assignment of statements to PODs. The solver minimizes the number of PODs
//! while respecting:
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

use std::collections::{BTreeSet, HashMap};

use crate::{
    frontend::{MainPod, MainPodBuilder, Operation, OperationArg},
    middleware::{Hash, MainPodProver, Params, Statement, VDSet, Value},
};

mod cost;
mod deps;
mod solver;

use cost::{AnchoredKeyId, StatementCost};
use deps::{DependencyGraph, StatementSource};
pub use solver::MultiPodSolution;

/// Error type for multi-POD operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    Custom(String),
    /// Error from the frontend.
    Frontend(#[from] crate::frontend::Error),
    /// Error from the MILP solver.
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
/// 2. **Solve**: Call [`solve`](Self::solve) to run the MILP solver, which determines
///    the optimal assignment of statements to PODs. This consumes the builder and
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
    /// Statements created by this builder.
    statements: Vec<Statement>,
    /// Operations that produce each statement.
    operations: Vec<Operation>,
    /// Optional initial wildcard values for custom operations
    operations_wildcard_values: Vec<Vec<(usize, Value)>>,
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
    operations_wildcard_values: Vec<Vec<(usize, Value)>>,
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

        let statements_in_this_pod: &Vec<usize> = &solution.pod_statements[pod_idx];
        let mut needed_external_pods: BTreeSet<usize> = BTreeSet::new();
        let mut needed_earlier_pods: BTreeSet<usize> = BTreeSet::new();

        // Step 1: Find which external and earlier PODs we need based on dependencies
        for &stmt_idx in statements_in_this_pod {
            for dep in &self.deps.statement_deps[stmt_idx] {
                match dep {
                    StatementSource::Internal(dep_idx) => {
                        // Check if dependency is in an earlier generated POD
                        let mut found = false;
                        for earlier_pod_idx in 0..pod_idx {
                            if solution.pod_public_statements[earlier_pod_idx].contains(dep_idx) {
                                needed_earlier_pods.insert(earlier_pod_idx);
                                found = true;
                                break;
                            }
                        }
                        // If not found in earlier PODs, it must be local to this POD
                        if !found && !statements_in_this_pod.contains(dep_idx) {
                            unreachable!(
                                "Internal dependency {} for statement {} is neither local \
                                 nor public in any earlier POD (solver bug)",
                                dep_idx, stmt_idx
                            );
                        }
                    }
                    StatementSource::External(pod_hash) => {
                        // Find which external POD has this hash
                        let ext_idx = self
                            .input_pods
                            .iter()
                            .position(|p| p.statements_hash() == *pod_hash);
                        match ext_idx {
                            Some(idx) => {
                                needed_external_pods.insert(idx);
                            }
                            None => {
                                unreachable!(
                                    "External dependency with hash {:?} not found in input PODs",
                                    pod_hash
                                );
                            }
                        }
                    }
                }
            }
        }

        // Step 2: Add input PODs to the builder
        for &ext_idx in &needed_external_pods {
            builder.add_pod(self.input_pods[ext_idx].clone())?;
        }
        for &earlier_idx in &needed_earlier_pods {
            builder.add_pod(earlier_pods[earlier_idx].clone())?;
        }

        // Step 3: Add statements in dependency order.
        // Statements are added in ascending index order, which matches dependency order:
        // if B depends on A, then A has a lower index and is added first.
        let statements_sorted: BTreeSet<usize> = statements_in_this_pod.iter().copied().collect();
        let public_set = &solution.pod_public_statements[pod_idx];

        // Track statements proved locally in this POD for argument remapping.
        // When an operation references a statement proved earlier in this same POD,
        // we need to use the Statement object that MainPodBuilder created (not the
        // original from MultiPodBuilder) so that find_op_arg can locate it.
        let mut added_statements: HashMap<usize, Statement> = HashMap::new();

        for &stmt_idx in &statements_sorted {
            let is_public = public_set.contains(&stmt_idx);
            let mut op = self.operations[stmt_idx].clone();
            let wildcard_values = self.operations_wildcard_values[stmt_idx].clone();

            // Remap Statement arguments that reference locally-proved statements.
            // For external dependencies (from input PODs including earlier generated PODs),
            // the original Statement is used directly - MainPodBuilder will find it in
            // the input POD's public statements via find_op_arg.
            for arg in &mut op.1 {
                if let OperationArg::Statement(ref orig_stmt) = arg {
                    // Find the original statement's index
                    if let Some(orig_idx) = self.statements.iter().position(|s| s == orig_stmt) {
                        // Get the remapped statement if it was proved locally in this POD
                        if let Some(remapped_stmt) = added_statements.get(&orig_idx) {
                            *arg = OperationArg::Statement(remapped_stmt.clone());
                        }
                    }
                }
            }

            let stmt = builder.op(is_public, wildcard_values, op)?;

            added_statements.insert(stmt_idx, stmt);
        }

        // Step 4: Prove the POD
        let pod = builder.prove(prover)?;

        Ok(pod)
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
            statements: Vec::new(),
            operations: Vec::new(),
            operations_wildcard_values: Vec::new(),
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

    pub fn op(
        &mut self,
        public: bool,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        let stmt = self.add_operation(wildcard_values, op)?;
        if public {
            // Index is always new (just added), so push without duplicate check
            self.output_public_indices.push(self.statements.len() - 1);
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

        self.statements.push(stmt.clone());
        self.operations.push(op);
        self.operations_wildcard_values.push(wildcard_values);

        Ok(stmt)
    }

    /// Mark a statement as public in output.
    ///
    /// Returns an error if the statement was not found in the builder.
    /// Calling this multiple times on the same statement is idempotent.
    pub fn reveal(&mut self, stmt: &Statement) -> Result<()> {
        if let Some(idx) = self.statements.iter().position(|s| s == stmt) {
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
    pub fn num_statements(&self) -> usize {
        self.statements.len()
    }

    /// Solve the packing problem and return a solved builder ready for proving.
    ///
    /// This runs the MILP solver to find the optimal POD assignment.
    /// Consumes the builder and returns a [`SolvedMultiPod`] that can be proved.
    pub fn solve(self) -> Result<SolvedMultiPod> {
        // Compute costs for each statement
        let costs: Vec<StatementCost> = self
            .operations
            .iter()
            .map(StatementCost::from_operation)
            .collect();

        // Collect all unique anchored keys from the costs
        let all_anchored_keys: Vec<AnchoredKeyId> = costs
            .iter()
            .flat_map(|c| c.anchored_keys.iter().cloned())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();

        // Build map from anchored key to its producing statement index (if any).
        // A Contains statement with literal (dict, key, value) "produces" that anchored key.
        let mut ak_to_producer: HashMap<AnchoredKeyId, usize> = HashMap::new();
        for (stmt_idx, stmt) in self.statements.iter().enumerate() {
            if let Some(ak) = AnchoredKeyId::from_contains_statement(stmt) {
                // First producer wins (shouldn't have duplicates in practice)
                ak_to_producer.entry(ak).or_insert(stmt_idx);
            }
        }

        // Build parallel array: anchored_key_producers[i] = producer for all_anchored_keys[i]
        let anchored_key_producers: Vec<Option<usize>> = all_anchored_keys
            .iter()
            .map(|ak| ak_to_producer.get(ak).copied())
            .collect();

        // Build external POD statement mapping
        let external_pod_statements = build_external_statement_map(&self.input_pods);

        // Build dependency graph
        let deps =
            DependencyGraph::build(&self.statements, &self.operations, &external_pod_statements);

        // Build statement content groups for deduplication.
        // Statements with identical content share a single slot in the POD.
        // Group statement indices by their content.
        let mut statement_content_group_index: HashMap<&Statement, usize> = HashMap::new();
        let mut statement_content_groups = Vec::new();
        for (idx, stmt) in self.statements.iter().enumerate() {
            use std::collections::hash_map::Entry;
            match statement_content_group_index.entry(stmt) {
                Entry::Vacant(e) => {
                    e.insert(statement_content_groups.len());
                    statement_content_groups.push(vec![idx]);
                }
                Entry::Occupied(e) => {
                    statement_content_groups[*e.get()].push(idx);
                }
            }
        }

        // Run solver
        let input = solver::SolverInput {
            num_statements: self.statements.len(),
            costs: &costs,
            deps: &deps,
            output_public_indices: &self.output_public_indices,
            params: &self.params,
            max_pods: self.options.max_pods,
            all_anchored_keys: &all_anchored_keys,
            anchored_key_producers: &anchored_key_producers,
            statement_content_groups: &statement_content_groups,
        };

        let solution = solver::solve(&input)?;

        Ok(SolvedMultiPod {
            params: self.params,
            vd_set: self.vd_set,
            input_pods: self.input_pods,
            statements: self.statements,
            operations: self.operations,
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

        // Solve
        let solved = builder.solve()?;
        // 8 statements / 4 per POD = 2 PODs minimum
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs for 8 statements with max_priv=4, got {}",
            solved.solution().pod_count
        );
        let pod_count = solved.solution().pod_count;

        // Prove and verify
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
        let parsed = parse(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            "#,
            &params,
            &[],
        )
        .expect("parse predicates");
        let batch = parsed
            .first_batch()
            .expect("parse predicates should have a batch");

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
        //   - POD 0 (intermediate): statements 0 (contains), 1 (a_out); a_out is public
        //   - POD 1 (output): statement 2 (b_out); b_out is public
        // The output POD accesses a_out from POD 0 to satisfy b_out's dependency.
        assert_eq!(
            solution.pod_count, 2,
            "Expected exactly 2 PODs for 3-statement chain with max_priv=2"
        );

        // POD 0 should contain statements 0 and 1 (contains and a_out)
        assert!(
            solution.pod_statements[0].contains(&0) && solution.pod_statements[0].contains(&1),
            "POD 0 should contain statements 0 (contains) and 1 (a_out), got {:?}",
            solution.pod_statements[0]
        );

        // Statement 1 (a_out) should be public in POD 0 so POD 1 can access it
        assert!(
            solution.pod_public_statements[0].contains(&1),
            "Statement 1 (a_out) should be public in POD 0"
        );

        // POD 1 (output) should contain statement 2 (b_out)
        assert!(
            solution.pod_statements[1].contains(&2),
            "POD 1 should contain statement 2 (b_out), got {:?}",
            solution.pod_statements[1]
        );

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

        let solved = builder.solve()?;

        // 6 statements / 2 per POD = 3 PODs minimum
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solved.solution().pod_count
        );

        // Prove and verify
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

        // Add 10 statements (requires 5 PODs). First one is public (required).
        let _ = builder.pub_op(FrontendOp::eq(0, 0));
        for i in 1..10 {
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
        multi_builder.add_pod(ext_pod_a.clone())?;
        multi_builder.add_pod(ext_pod_b.clone())?;

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

        let solved = multi_builder.solve()?;
        assert!(
            solved.solution().pod_count >= 2,
            "Expected at least 2 PODs, got {}",
            solved.solution().pod_count
        );

        let result = solved.prove(&prover)?;

        // Verify all PODs
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
        multi_builder.add_pod(ext_pod_a)?;
        multi_builder.add_pod(ext_pod_b)?;
        multi_builder.add_pod(ext_pod_c)?;

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

        let solved = builder.solve()?;
        // 4 SignedBy / 2 per POD = exactly 2 PODs
        assert_eq!(
            solved.solution().pod_count,
            2,
            "Expected exactly 2 PODs for 4 SignedBy with max_signed_by=2, got {}",
            solved.solution().pod_count
        );
        let pod_count = solved.solution().pod_count;

        // Prove and verify
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
        let parsed = parse(
            r#"
            pred_a(X) = AND(Contains(X, "k", 1))
            pred_b(X) = AND(pred_a(X))
            pred_c(X) = AND(pred_b(X))
            pred_d(X) = AND(pred_c(X))
            "#,
            &params,
            &[],
        )
        .expect("parse predicates");
        let batch = parsed
            .first_batch()
            .expect("parse predicates should have a batch");

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
        let parsed = parse(
            r#"
            pred_b(X) = AND(Contains(X, "k", 1))
            pred_c(X) = AND(Contains(X, "k", 1))
            pred_a(X, Y) = AND(
                pred_b(X)
                pred_c(Y)
            )
            "#,
            &params,
            &[],
        )
        .expect("parse predicates");
        let batch = parsed
            .first_batch()
            .expect("parse predicates should have a batch");

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
}
