//! Multi-POD builder for the Merkle statement tree design.
//!
//! See `docs/multipod_merkle_statement_tree.md` for the design overview.
//!
//! This is a parallel implementation alongside `super::multi_pod`. The old
//! solver remains in place during development; once the new POD circuit
//! lands, this module replaces `multi_pod` and that module is removed.
//!
//! The solver is purely symbolic: it consumes a positional [`InputShape`]
//! and produces a positional [`OutputShape`]. The build layer in this
//! module translates between user-facing builder state and the symbolic
//! representation, holding an internal side table that maps positional
//! indices back to concrete pod hashes and external (input) statements.
//!
//! `solve()` partitions the workload symbolically; `prove()` then walks
//! the partition and builds + proves each POD in chain order.
//!
//! The module is not yet re-exported from `frontend::mod`; until it is,
//! the public surface is reachable only from tests, so we silence
//! dead-code warnings module-wide.

#![allow(dead_code)]

use std::{
    collections::{hash_map::Entry, BTreeSet, HashMap, HashSet},
    fmt,
};

use crate::{
    frontend::{MainPod, MainPodBuilder, Operation},
    middleware::{
        Hash, InputPodOpenStatement, MainPodProver, NativeOperation, OperationAux, OperationType,
        Params, Statement, VDSet, Value, BASE_PARAMS,
    },
};

mod cost;
mod deps;
mod diagnostics;
mod partition;
#[cfg(any(test, feature = "milp"))]
mod partition_milp;
mod shape;

use cost::StatementCost;
use deps::{DependencyGraph, ExternalDependency, StatementSource};
pub use diagnostics::{ResourceSummary, SolutionBreakdown};
pub use shape::{AbstractDep, InputShape, OutputShape};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    Custom(String),
    Frontend(#[from] crate::frontend::Error),
    NoFeasiblePartition(String),
    ChainTreeCapacityExceeded { needed: usize, capacity: usize },
    MilpUnavailable,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Custom(msg) => write!(f, "Custom error: {}", msg),
            Error::Frontend(e) => write!(f, "Frontend error: {}", e),
            Error::NoFeasiblePartition(msg) => {
                write!(f, "No feasible partition: {}", msg)
            }
            Error::ChainTreeCapacityExceeded { needed, capacity } => write!(
                f,
                "Chain tree capacity exceeded: partition would publish {} \
                 statements across the chain but the public-statements MT \
                 has capacity {}",
                needed, capacity
            ),
            Error::MilpUnavailable => write!(
                f,
                "MILP solver requested but the `milp` feature is not enabled"
            ),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

/// Which solver `MultiPodBuilder::solve_with` should run against the
/// problem. `Milp` requires the `milp` Cargo feature (or a test build);
/// requesting it from a feature-off release build returns
/// [`Error::MilpUnavailable`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SolverKind {
    /// Production DP partitioner with bin-packing + random-priority Kahn
    /// orderings. Polynomial time, no external solver dependency.
    Heuristic,
    /// MILP oracle (via `good_lp` / SCIP). Optimal K but non-linear time
    /// growth on hard instances. Intended for offline use against a
    /// captured `InputShape`; not recommended for interactive solve paths.
    Milp,
}

impl fmt::Display for SolverKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverKind::Heuristic => write!(f, "Heuristic solver"),
            SolverKind::Milp => write!(f, "MILP solver"),
        }
    }
}

/// Side table pairing an [`OutputShape`]'s positional external indices
/// with the concrete pod hashes and input statements they refer to. The
/// solver never sees concrete data; the build layer uses this index to
/// reattach hashes when materialising a [`MultiPodResult`] from a
/// partition.
#[derive(Clone, Debug)]
struct ExternalIndex {
    pods: Vec<Hash>,
    statements: Vec<ExternalDependency>,
    /// Inverse of `pods` for O(1) hash → abstract-pod-index lookup.
    pod_index_by_hash: HashMap<Hash, usize>,
}

impl ExternalIndex {
    fn new(pods: Vec<Hash>, statements: Vec<ExternalDependency>) -> Self {
        let pod_index_by_hash = pods.iter().copied().zip(0..).collect();
        Self {
            pods,
            statements,
            pod_index_by_hash,
        }
    }
}

pub struct MultiPodBuilder {
    params: Params,
    vd_set: VDSet,
    input_pods: Vec<MainPod>,
    operations_wildcard_values: HashMap<usize, Vec<(usize, Value)>>,
    output_public_indices: Vec<usize>,
    builder: MainPodBuilder,
}

impl MultiPodBuilder {
    pub fn new(params: &Params, vd_set: &VDSet) -> Self {
        let unlimited_params = Params {
            max_statements: usize::MAX / 2,
            max_input_pods: usize::MAX / 2,
            max_open_input_statements: usize::MAX / 2,
            ..params.clone()
        };
        let builder = MainPodBuilder::new(&unlimited_params, vd_set);
        Self {
            params: params.clone(),
            vd_set: vd_set.clone(),
            input_pods: Vec::new(),
            operations_wildcard_values: HashMap::new(),
            output_public_indices: Vec::new(),
            builder,
        }
    }

    pub fn add_pod(&mut self, pod: MainPod) -> Result<()> {
        self.builder.add_pod(pod.clone())?;
        self.input_pods.push(pod);
        Ok(())
    }

    pub fn pub_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(true, vec![], op)
    }

    pub fn priv_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(false, vec![], op)
    }

    pub fn op(
        &mut self,
        public: bool,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        let (stmt, idx) = self.add_operation(wildcard_values, op)?;
        if public {
            self.mark_public(idx);
        }
        Ok(stmt)
    }

    fn add_operation(
        &mut self,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<(Statement, usize)> {
        let stmt = self.builder.op(false, wildcard_values.clone(), op)?;
        let idx = self.stmt_index(&stmt);
        self.operations_wildcard_values.insert(idx, wildcard_values);
        Ok((stmt, idx))
    }

    fn stmt_index(&self, stmt: &Statement) -> usize {
        self.builder
            .statements
            .iter()
            .position(|(_, s)| s == stmt)
            .expect("statement exists in builder")
    }

    fn mark_public(&mut self, idx: usize) {
        if !self.output_public_indices.contains(&idx) {
            self.output_public_indices.push(idx);
        }
    }

    pub fn reveal(&mut self, stmt: &Statement) -> Result<()> {
        let idx = self
            .builder
            .statements
            .iter()
            .position(|(_, s)| s == stmt)
            .ok_or_else(|| {
                Error::Custom("reveal() called with statement not found in builder".to_string())
            })?;
        self.mark_public(idx);
        Ok(())
    }

    pub fn stmt_len(&self) -> usize {
        self.builder.stmt_len()
    }

    /// Read-only view of the inner builder's recorded operations. Same
    /// indexing as [`InputShape::costs`] / [`InputShape::dep_edges`], so
    /// callers can map a positional cost back to the operation that
    /// produced it.
    pub fn operations(&self) -> &[Operation] {
        &self.builder.operations
    }

    /// Snapshot of the inner builder's recorded statements. Same
    /// indexing as [`Self::operations`].
    pub fn statements(&self) -> Vec<Statement> {
        self.builder
            .statements
            .iter()
            .map(|(_, s)| s.clone())
            .collect()
    }

    /// Read-only view of the input PODs this builder will reference as
    /// external sources. Indices match the `pod` field of
    /// [`AbstractDep::External`] entries in [`Self::input_shape`].
    pub fn input_pods(&self) -> &[MainPod] {
        &self.input_pods
    }

    /// Compute the symbolic [`InputShape`] without running the
    /// partitioner. Useful for capturing fixtures from a real builder
    /// run and inspecting the shape before solving.
    pub fn input_shape(&self) -> InputShape {
        let external_pod_statements = build_external_statement_map(&self.input_pods);
        let statements: Vec<Statement> = self
            .builder
            .statements
            .iter()
            .map(|(_, s)| s.clone())
            .collect();
        let deps = DependencyGraph::build(
            &statements,
            &self.builder.operations,
            &external_pod_statements,
        );
        let (shape, _) = build_shape_and_index(
            &self.builder.operations,
            &deps,
            &self.output_public_indices,
            &self.params,
        );
        shape
    }

    /// Pre-solve resource summary. Aggregates per-statement costs against
    /// per-POD limits and identifies the bottleneck resource.
    pub fn resource_summary(&self) -> ResourceSummary {
        let costs: Vec<StatementCost> = self
            .builder
            .operations
            .iter()
            .map(|op| StatementCost::from_operation(op, &self.params))
            .collect();
        ResourceSummary::from_costs(costs.iter(), &self.params)
    }

    /// Solve the partitioning problem with the production heuristic.
    /// Shorthand for [`Self::solve_with`] with [`SolverKind::Heuristic`].
    pub fn solve(self) -> Result<SolvedMultiPod> {
        self.solve_with(SolverKind::Heuristic)
    }

    /// Solve the partitioning problem. Builds the [`InputShape`] from the
    /// current builder state (including the external-republish pre-pass),
    /// runs the requested partitioner, and returns a [`SolvedMultiPod`]
    /// that holds the partition and the side data needed to materialise
    /// PODs.
    ///
    /// Returns [`Error::MilpUnavailable`] if `kind == SolverKind::Milp`
    /// in a release build without the `milp` feature.
    pub fn solve_with(self, kind: SolverKind) -> Result<SolvedMultiPod> {
        let MainPodBuilder {
            statements: stmt_pairs,
            operations,
            ..
        } = self.builder;
        let statements: Vec<Statement> = stmt_pairs.into_iter().map(|(_, s)| s).collect();

        let external_pod_statements = build_external_statement_map(&self.input_pods);
        let deps = DependencyGraph::build(&statements, &operations, &external_pod_statements);

        let (shape, external_index) = build_shape_and_index(
            &operations,
            &deps,
            &self.output_public_indices,
            &self.params,
        );

        let mut output = run_partition(&shape, kind)?;

        // Synthetic republish statements appear at positions >= operations.len()
        // in the augmented shape, each with one External dep recording its
        // input statement. Whichever POD a synthetic lands in republishes
        // that input statement.
        let n_orig = operations.len();
        let mut new_republished: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); output.pod_count];
        for (pod_idx, stmts) in output.pod_statements.iter().enumerate() {
            for &s in stmts {
                if s >= n_orig {
                    if let AbstractDep::External { statement, .. } = shape.dep_edges[s][0] {
                        new_republished[pod_idx].insert(statement);
                    }
                }
            }
        }
        output.pod_republished_externals = new_republished;

        let public_sets = intermediate_public_sets(&shape, &output);
        let chain_total: usize = public_sets
            .iter()
            .take(output.pod_count.saturating_sub(1))
            .map(|s| s.len())
            .sum();
        let chain_capacity = 2 << BASE_PARAMS.max_depth_public_statements_mt;
        if chain_total > chain_capacity {
            return Err(Error::ChainTreeCapacityExceeded {
                needed: chain_total,
                capacity: chain_capacity,
            });
        }

        let input_pod_idx_by_abs: Vec<usize> = external_index
            .pods
            .iter()
            .map(|h| {
                self.input_pods
                    .iter()
                    .position(|p| p.statements_hash() == *h)
                    .expect("external pod referenced by user op is in input_pods")
            })
            .collect();

        Ok(SolvedMultiPod {
            params: self.params,
            vd_set: self.vd_set,
            input_pods: self.input_pods,
            statements,
            operations,
            output_public_indices: self.output_public_indices,
            operations_wildcard_values: self.operations_wildcard_values,
            shape,
            output,
            external_index,
            input_pod_idx_by_abs,
            public_sets,
        })
    }
}

/// A solved multi-POD problem. Carries the partition plus everything
/// needed to materialise concrete PODs once the new circuit lands.
pub struct SolvedMultiPod {
    params: Params,
    vd_set: VDSet,
    input_pods: Vec<MainPod>,
    statements: Vec<Statement>,
    operations: Vec<Operation>,
    output_public_indices: Vec<usize>,
    operations_wildcard_values: HashMap<usize, Vec<(usize, Value)>>,
    shape: InputShape,
    output: OutputShape,
    external_index: ExternalIndex,
    /// `external_index.pods[abs_pod]` is a hash; this maps that
    /// abstract index to the matching POD's position in `input_pods`,
    /// so `pod_inputs` can attach the right `MainPod` without scanning.
    input_pod_idx_by_abs: Vec<usize>,
    /// Per-POD public sets. Computed once at `solve()` for the chain-tree
    /// capacity check and reused by `prove()`.
    public_sets: Vec<BTreeSet<usize>>,
}

impl SolvedMultiPod {
    pub fn input_shape(&self) -> &InputShape {
        &self.shape
    }

    pub fn solution(&self) -> &OutputShape {
        &self.output
    }

    pub fn solution_breakdown(&self) -> SolutionBreakdown {
        SolutionBreakdown::from_solution(&self.shape, &self.output)
    }

    /// Number of original user-added operations. Statement positions in
    /// `solution().pod_statements` at or beyond this index are synthetic
    /// republish statements (zero cost, one external dep).
    pub fn num_original_statements(&self) -> usize {
        self.operations.len()
    }

    /// Build and prove all PODs in the partition in chain order. Each
    /// intermediate POD extends its chain predecessor's public statement
    /// tree (slot 0) and appends only the statements downstream consumers
    /// will open. The output POD does not extend; it materialises a fresh
    /// public statement tree containing exactly `output_public_indices`,
    /// importing any upstream-produced output-publics through slot 0.
    pub fn prove(self, prover: &dyn MainPodProver) -> Result<MultiPodResult> {
        let pod_count = self.output.pod_count;
        let mut pods: Vec<MainPod> = Vec::with_capacity(pod_count);
        for p in 0..pod_count {
            let pod = self.build_single_pod(p, &pods, prover)?;
            pods.push(pod);
        }
        Ok(MultiPodResult { pods })
    }

    fn build_single_pod(
        &self,
        p: usize,
        earlier_pods: &[MainPod],
        prover: &dyn MainPodProver,
    ) -> Result<MainPod> {
        let is_output = p + 1 == self.output.pod_count;
        let mut builder = MainPodBuilder::new(&self.params, &self.vd_set);

        let (inputs, ext_slot) = self.pod_inputs(p, earlier_pods);
        for input in inputs {
            builder.add_pod(input)?;
        }

        if p > 0 && !is_output {
            builder.extend_input_pod0_public_statements();
        }

        let n_orig = self.operations.len();
        let public_set = &self.public_sets[p];
        for &s in &self.output.pod_statements[p] {
            if s >= n_orig {
                // Synthetic republish: open the input statement so
                // downstream PODs can read it from the chain at slot 0.
                let AbstractDep::External { pod, statement } = &self.shape.dep_edges[s][0] else {
                    unreachable!("synthetic statement must have a single External dep");
                };
                let slot = ext_slot[pod];
                let stmt = self.external_index.statements[*statement].statement.clone();
                builder.open_input_st(true, slot, &stmt)?;
                continue;
            }
            let public = !is_output && public_set.contains(&s);
            if let OperationType::Native(NativeOperation::OpenInputStatement) =
                &self.operations[s].0
            {
                // Staging-time aux carries a `pod_index` from the staging
                // builder's input slots; re-issue against this POD's
                // ext_slot mapping.
                let OperationAux::OpenInputStatement(InputPodOpenStatement { sts_root, .. }) =
                    &self.operations[s].2
                else {
                    unreachable!("OpenInputStatement op without InputPodOpenStatement aux");
                };
                let abs_pod = *self
                    .external_index
                    .pod_index_by_hash
                    .get(sts_root)
                    .expect("staging OpenInputStatement's source pod is in external_index");
                let slot = ext_slot[&abs_pod];
                builder.open_input_st(public, slot, &self.statements[s])?;
                continue;
            }
            let wildcards = self
                .operations_wildcard_values
                .get(&s)
                .cloned()
                .unwrap_or_default();
            builder.op(public, wildcards, self.operations[s].clone())?;
        }

        if is_output {
            for &idx in &self.output_public_indices {
                let stmt = &self.statements[idx];
                if builder.statements.iter().any(|(_, s)| s == stmt) {
                    builder.reveal(stmt)?;
                } else {
                    // Output-public produced upstream — open from chain.
                    builder.open_input_st(true, 0, stmt)?;
                }
            }
        }

        builder.prove(prover).map_err(Error::from)
    }

    /// For POD `p`: the concrete `MainPod`s to install as inputs (chain
    /// predecessor at slot 0 if any, externals at slots 1+) plus a map
    /// from abstract external-pod index to builder slot. The slot map
    /// drives `open_input_st` calls for synthetics and staging-Opens.
    fn pod_inputs(
        &self,
        p: usize,
        earlier_pods: &[MainPod],
    ) -> (Vec<MainPod>, HashMap<usize, usize>) {
        let mut inputs: Vec<MainPod> = Vec::new();
        if p > 0 {
            inputs.push(earlier_pods[p - 1].clone());
        }
        let mut refs: BTreeSet<usize> = BTreeSet::new();
        for &s in &self.output.pod_statements[p] {
            for dep in &self.shape.dep_edges[s] {
                if let AbstractDep::External { pod, .. } = dep {
                    refs.insert(*pod);
                }
            }
        }
        let mut ext_slot: HashMap<usize, usize> = HashMap::new();
        for abs_pod in refs {
            let pod_idx = self.input_pod_idx_by_abs[abs_pod];
            ext_slot.insert(abs_pod, inputs.len());
            inputs.push(self.input_pods[pod_idx].clone());
        }
        (inputs, ext_slot)
    }
}

pub struct MultiPodResult {
    pub pods: Vec<MainPod>,
}

impl MultiPodResult {
    pub fn output_pod(&self) -> &MainPod {
        self.pods.last().expect("at least one POD")
    }

    pub fn intermediate_pods(&self) -> &[MainPod] {
        &self.pods[..self.pods.len() - 1]
    }
}

/// Dispatch to the requested solver. The MILP arm is only present when
/// the `milp` feature is enabled (always the case in test builds via
/// `[dev-dependencies] good_lp`); otherwise it returns
/// [`Error::MilpUnavailable`].
fn run_partition(shape: &InputShape, kind: SolverKind) -> Result<OutputShape> {
    let outcome = match kind {
        SolverKind::Heuristic => partition::partition(shape),
        SolverKind::Milp => {
            #[cfg(any(test, feature = "milp"))]
            {
                partition_milp::solve(shape)
            }
            #[cfg(not(any(test, feature = "milp")))]
            {
                let _ = shape;
                return Err(Error::MilpUnavailable);
            }
        }
    };
    outcome.ok_or_else(|| {
        Error::NoFeasiblePartition(format!(
            "the {} could not find a feasible partition under the current \
             params; run diagnose_failure() for details",
            kind
        ))
    })
}

/// Per-POD public-set decisions: which statements each intermediate POD
/// must reveal so downstream PODs (and the output POD) can reach them
/// through the chain tree.
///
/// Three rules combine:
/// 1. **Downstream consumption**: any statement consumed by a later POD via
///    `AbstractDep::Internal` must be public at its producer. This also
///    covers synthetics whose consumers live downstream (their republish
///    is exactly this case).
/// 2. **Output-public flow-up**: any statement in `output_public_indices`
///    produced upstream of the output POD must be revealed by its
///    producer so the output POD can `open_input_st` it through slot 0.
/// 3. **Output POD**: the last POD's set is left empty here. The build
///    layer handles its fresh public tree separately (no `extend`).
///
/// Indexed by POD position. Entry `pod_count - 1` is always empty.
fn intermediate_public_sets(shape: &InputShape, output: &OutputShape) -> Vec<BTreeSet<usize>> {
    let pod_count = output.pod_count;
    let mut sets: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); pod_count];
    if pod_count == 0 {
        return sets;
    }

    let n = shape.num_statements();
    let mut pod_of: Vec<Option<usize>> = vec![None; n];
    for (p, stmts) in output.pod_statements.iter().enumerate() {
        for &s in stmts {
            pod_of[s] = Some(p);
        }
    }
    let output_pod = pod_count - 1;

    // Rule 1: downstream-consumed statements get revealed by their producer.
    for (consumer, deps) in shape.dep_edges.iter().enumerate() {
        let consumer_pod = match pod_of[consumer] {
            Some(p) => p,
            None => continue,
        };
        for dep in deps {
            if let AbstractDep::Internal(producer) = dep {
                if let Some(producer_pod) = pod_of[*producer] {
                    if producer_pod < consumer_pod {
                        sets[producer_pod].insert(*producer);
                    }
                }
            }
        }
    }

    // Rule 2: output-public statements produced upstream of the output POD.
    for &s in &shape.output_public_indices {
        if let Some(producer_pod) = pod_of[s] {
            if producer_pod < output_pod {
                sets[producer_pod].insert(s);
            }
        }
    }

    sets
}

/// Index every public statement of every input POD by content. The dep
/// graph uses this to recognise when a statement argument refers to an
/// externally-provided POD's public statement rather than a locally-built
/// one.
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

/// Convert a concrete `DependencyGraph` into the positional `InputShape`
/// the solver consumes.
///
/// Also runs the external-republish pre-pass: input statements with two
/// or more downstream consumers are rewritten as synthetic "republish"
/// statements (zero cost, one `External` dep) appended after the original
/// statement list. Consumers' deps that pointed at those input statements
/// become `Internal` references to the synthetic position. Whichever POD
/// the DP places a synthetic into pays one external-input slot for that
/// input statement; every downstream consumer reaches it via slot 0
/// (chain) for one import slot. With multiple consumers, this saves at
/// least one external-input slot net.
///
/// Returns the [`InputShape`] and the side-table [`ExternalIndex`]. Each
/// synthetic statement's single [`AbstractDep::External`] dep records the
/// input statement it republishes, so callers can recover the
/// synthetic-to-statement mapping from `shape.dep_edges` directly.
fn build_shape_and_index(
    operations: &[Operation],
    deps: &DependencyGraph,
    output_public_indices: &[usize],
    params: &Params,
) -> (InputShape, ExternalIndex) {
    let n_orig = operations.len();

    let mut external_pods: Vec<Hash> = Vec::new();
    let mut pod_idx: HashMap<Hash, usize> = HashMap::new();
    let mut external_statements: Vec<ExternalDependency> = Vec::new();
    let mut external_statement_idx: HashMap<ExternalDependency, usize> = HashMap::new();
    let mut statement_pod: Vec<usize> = Vec::new();

    for edges in &deps.statement_deps {
        for src in edges {
            if let StatementSource::External(ext) = src {
                if let Entry::Vacant(e) = pod_idx.entry(ext.pod_hash) {
                    e.insert(external_pods.len());
                    external_pods.push(ext.pod_hash);
                }
                if let Entry::Vacant(e) = external_statement_idx.entry(ext.clone()) {
                    e.insert(external_statements.len());
                    external_statements.push(ext.clone());
                    statement_pod.push(pod_idx[&ext.pod_hash]);
                }
            }
        }
    }

    // Count downstream consumers per input statement. Dedupe within a
    // single consumer's dep list (multiple deps on the same input
    // statement from one consumer still count as one consumer).
    let mut statement_consumer_count = vec![0_usize; external_statements.len()];
    for edges in &deps.statement_deps {
        let mut seen: HashSet<usize> = HashSet::new();
        for src in edges {
            if let StatementSource::External(ext) = src {
                let u = external_statement_idx[ext];
                if seen.insert(u) {
                    statement_consumer_count[u] += 1;
                }
            }
        }
    }

    // Feasibility-driven republish: a statement's POD imports one slot
    // for chain (if any dep flows through it) plus one slot per distinct
    // external pod the statement directly references. When the sum
    // exceeds `max_input_pods`, the POD cannot fit -- we must republish
    // enough of the statement's input statements so they reach the
    // consumer through the chain instead. Mark those input statements
    // here; the synthetic allocation loop below unions this with the
    // 2+ consumers rule.
    //
    // Republishing any input statement forces chain use at the consumer
    // site, so the post-republish budget is
    // `(K - R) + 1 <= max_input_pods`, i.e.
    // `R >= K - max_input_pods + 1` whenever the original
    // `K + chain_used` would have busted the cap.
    let max_input_pods = params.max_input_pods;
    let mut must_republish: Vec<bool> = vec![false; external_statements.len()];
    for edges in &deps.statement_deps {
        let mut distinct_pods: BTreeSet<usize> = BTreeSet::new();
        let mut has_internal = false;
        let mut statements_by_pod: HashMap<usize, Vec<usize>> = HashMap::new();
        for src in edges {
            match src {
                StatementSource::Internal(_) => has_internal = true,
                StatementSource::External(ext) => {
                    let pod = pod_idx[&ext.pod_hash];
                    let statement = external_statement_idx[ext];
                    distinct_pods.insert(pod);
                    statements_by_pod.entry(pod).or_default().push(statement);
                }
            }
        }
        let k = distinct_pods.len();
        let chain_already_used = if has_internal { 1 } else { 0 };
        if k + chain_already_used <= max_input_pods {
            continue;
        }
        // Republish R pods. After republishing, chain is in use, so we
        // need (K - R) + 1 <= max_input_pods.
        let r = k + 1 - max_input_pods;
        // Pick the highest-numbered pods first (deterministic). The
        // chosen pods drop out of the consumer's direct refs.
        for pod in distinct_pods.iter().rev().take(r) {
            for &statement in &statements_by_pod[pod] {
                must_republish[statement] = true;
            }
        }
    }

    // Opportunistic external-pod bundling: if any input statement from
    // external pod E is already being republished (multi-consumer or
    // feasibility), republish all of E's used input statements. The
    // synth-hosting POD already pays one input-pod slot for E, so
    // bundling its other input statements is marginal cost there and
    // frees downstream consumers from re-referencing E. See
    // `docs/multipod_merkle_statement_tree.md`.
    let mut bundled_pods: HashSet<usize> = HashSet::new();
    for u in 0..external_statements.len() {
        if statement_consumer_count[u] >= 2 || must_republish[u] {
            bundled_pods.insert(statement_pod[u]);
        }
    }
    for u in 0..external_statements.len() {
        if bundled_pods.contains(&statement_pod[u]) {
            must_republish[u] = true;
        }
    }

    // Allocate a synthetic statement for each input statement with 2+
    // consumers OR flagged by the feasibility pre-pass above.
    // `synthetic_to_statement[i]` is the input-statement index of the
    // (n_orig + i)-th statement.
    let mut synthetic_to_statement: Vec<usize> = Vec::new();
    let mut statement_to_synthetic: Vec<Option<usize>> = vec![None; external_statements.len()];
    for u in 0..external_statements.len() {
        if statement_consumer_count[u] >= 2 || must_republish[u] {
            let synth_idx = n_orig + synthetic_to_statement.len();
            statement_to_synthetic[u] = Some(synth_idx);
            synthetic_to_statement.push(u);
        }
    }
    let n_synth = synthetic_to_statement.len();

    // Augmented costs: originals + zero costs for synthetics.
    let mut costs: Vec<StatementCost> = operations
        .iter()
        .map(|op| StatementCost::from_operation(op, params))
        .collect();
    costs.extend((0..n_synth).map(|_| StatementCost::default()));

    // Augmented dep_edges. Original statements: External(pod, statement)
    // becomes Internal(synth_idx) when the input statement is being
    // republished. Synthetic statements: each has one External dep to
    // its input statement.
    let mut dep_edges: Vec<Vec<AbstractDep>> = deps
        .statement_deps
        .iter()
        .map(|edges| {
            edges
                .iter()
                .map(|src| match src {
                    StatementSource::Internal(d) => AbstractDep::Internal(*d),
                    StatementSource::External(ext) => {
                        let u = external_statement_idx[ext];
                        if let Some(synth_idx) = statement_to_synthetic[u] {
                            AbstractDep::Internal(synth_idx)
                        } else {
                            AbstractDep::External {
                                pod: pod_idx[&ext.pod_hash],
                                statement: u,
                            }
                        }
                    }
                })
                .collect()
        })
        .collect();
    for &u in &synthetic_to_statement {
        let ext = &external_statements[u];
        dep_edges.push(vec![AbstractDep::External {
            pod: pod_idx[&ext.pod_hash],
            statement: u,
        }]);
    }

    let shape = InputShape {
        costs,
        dep_edges,
        output_public_indices: output_public_indices.to_vec(),
        num_external_pods: external_pods.len(),
        statement_pod,
        params: params.clone(),
    };
    let index = ExternalIndex::new(external_pods, external_statements);
    (shape, index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        backends::plonky2::mock::mainpod::MockProver, examples::MOCK_VD_SET,
        frontend::Operation as FrontendOp,
    };

    #[test]
    fn end_to_end_solve_single_pod() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.pub_op(FrontendOp::eq(1, 1)).expect("op should add");

        let solved = builder.solve().expect("should solve");
        assert_eq!(solved.solution().pod_count, 1);
        assert_eq!(solved.solution().pod_statements[0].len(), 1);
    }

    /// Smoke test that `SolverKind::Milp` reaches the MILP backend.
    #[test]
    fn solve_with_milp_kind_uses_oracle() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.pub_op(FrontendOp::eq(1, 1)).expect("op should add");

        let solved = builder
            .solve_with(SolverKind::Milp)
            .expect("MILP should solve a trivial input");
        assert_eq!(solved.solution().pod_count, 1);
        assert_eq!(solved.solution().pod_statements[0].len(), 1);
    }

    #[test]
    fn end_to_end_solve_forces_split() {
        // Tight max_statements forces splitting into 2 PODs.
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        // 3 independent statements need 2 PODs at max_statements = 2.
        for i in 0..3_i64 {
            builder.priv_op(FrontendOp::eq(i, i)).expect("priv op");
        }
        builder.pub_op(FrontendOp::eq(100, 100)).expect("pub op");

        let solved = builder.solve().expect("should solve");
        assert!(solved.solution().pod_count >= 2);
    }

    #[test]
    fn prove_single_pod() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.pub_op(FrontendOp::eq(1, 1)).expect("op should add");

        let solved = builder.solve().expect("should solve");
        assert_eq!(solved.solution().pod_count, 1);
        let result = solved.prove(&MockProver {}).expect("prove should succeed");
        assert_eq!(result.pods.len(), 1);
        result.pods[0].pod.verify().expect("pod verifies");
    }

    #[test]
    fn prove_cross_pod_custom_predicate_chain() {
        // pred_b(X) wraps pred_a(X) wraps Contains(X, "k", 1). With
        // max_statements = 2, the three resulting statements must split
        // across PODs, so the output POD's b_out has to reach back
        // through the chain tree to consume the intermediate pred_a /
        // Contains it depends on.
        use crate::{dict, lang::load_module};

        let params = Params {
            max_statements: 2,
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
        let contains = builder
            .priv_op(FrontendOp::dict_contains(dict, "k", 1))
            .expect("contains");
        let a_out = builder
            .priv_op(FrontendOp::custom(
                batch.predicate_ref_by_name("pred_a").unwrap(),
                [contains],
            ))
            .expect("pred_a");
        let _b_out = builder
            .pub_op(FrontendOp::custom(
                batch.predicate_ref_by_name("pred_b").unwrap(),
                [a_out],
            ))
            .expect("pred_b");

        let solved = builder.solve().expect("should solve");
        assert!(solved.solution().pod_count >= 2);
        let result = solved.prove(&MockProver {}).expect("prove should succeed");
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|e| panic!("POD {} verification failed: {:?}", i, e));
        }
    }

    #[test]
    fn prove_chain_two_pods() {
        // Tight max_statements forces splitting; verifies that chain
        // monotonicity (extend_input_pod0_public_statements) carries the
        // intermediate POD's statement forward so the output POD can
        // reach it.
        let params = Params {
            max_statements: 2,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        for i in 0..3_i64 {
            builder.priv_op(FrontendOp::eq(i, i)).expect("priv op");
        }
        builder.pub_op(FrontendOp::eq(100, 100)).expect("pub op");

        let solved = builder.solve().expect("should solve");
        assert!(solved.solution().pod_count >= 2);
        let result = solved.prove(&MockProver {}).expect("prove should succeed");
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|e| panic!("POD {} verification failed: {:?}", i, e));
        }
    }

    #[test]
    fn prove_with_external_pod_arg() {
        // User-adds an external pod and passes one of its public
        // statements directly as an op arg (via a custom predicate that
        // wraps it). Exercises the staging auto-import path:
        // `MainPodBuilder::ensure_statement` emits an
        // `OpenInputStatement` op at staging time, the dep graph models
        // it as an External-dep node, and replay re-issues the open
        // against the per-POD builder's slot.
        use crate::lang::load_module;

        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        let module = load_module(
            r#"
            pred_a(X) = AND(Lt(X, 2))
            "#,
            "test",
            &params,
            &[],
        )
        .expect("load module");
        let batch = &module.batch;

        let mut ext_builder = MainPodBuilder::new(&params, vd_set);
        ext_builder
            .pub_op(FrontendOp::lt(1, 2))
            .expect("ext pub op");
        let ext_pod = ext_builder.prove(&prover).expect("ext prove");
        let ext_stmt = ext_pod
            .pod
            .pub_statements()
            .into_iter()
            .find(|s| !s.is_none())
            .expect("ext pod has a public statement");

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        builder.add_pod(ext_pod).expect("add ext pod");
        builder
            .pub_op(FrontendOp::custom(
                batch.predicate_ref_by_name("pred_a").unwrap(),
                [ext_stmt],
            ))
            .expect("pred_a on ext stmt");

        let solved = builder.solve().expect("should solve");
        let result = solved.prove(&prover).expect("prove should succeed");
        assert!(!result.pods.is_empty());
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|e| panic!("POD {} verification failed: {:?}", i, e));
        }
    }

    /// Captured `multi_pod_tree::InputShape` for zk-craft's
    /// `CraftRefineryCracked` action (episode-1 plugin). Used to
    /// stress-test the partitioner against a realistic, large input.
    /// See `sdk/src/tests.rs::capture_cracked_refinery_input_shape`
    /// in the zk-craft repo for how the fixture is regenerated.
    const CRACKED_REFINERY_FIXTURE: &str = include_str!("tests/fixtures/cracked_refinery.json");

    /// Pins partition quality on the cracked-refinery fixture. The
    /// resource-induced lower bound (`max_r ceil(total_r / cap_r)` over
    /// per-statement-summable resources) is K=12, driven by 96
    /// custom-predicate verifications at cap 8/POD. Under statement-
    /// table accounting, per-POD publish cap (`max_public_statements
    /// = 20`), coupling-aware bin-packing tiebreak (admit ready
    /// statements whose Internal deps already sit in the current
    /// segment first), and dynamic export tracking (the publish-cap
    /// counter releases a segment slot when an admitted statement
    /// absorbs its dep's last unfinished consumer), the heuristic
    /// reaches K=13. MILP+cap reaches K=12, so the gap is 1 POD. See
    /// `docs/multipod_merkle_statement_tree.md` ("Custom predicate
    /// body+head locality" and "Future generators under consideration")
    /// for the structural reason and candidates that might close it.
    #[test]
    fn cracked_refinery_fixture_partitions() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        assert_eq!(shape.num_statements(), 345);

        let outcome = partition::partition(&shape);
        match outcome {
            Some(out) => {
                eprintln!(
                    "cracked refinery partitioned into {} PODs, sizes={:?}",
                    out.pod_count,
                    out.pod_statements
                        .iter()
                        .map(|v| v.len())
                        .collect::<Vec<_>>()
                );
                let breakdown = diagnostics::SolutionBreakdown::from_solution(&shape, &out);
                eprintln!("{}", breakdown);
                eprintln!("POD 0 stmt indices: {:?}", out.pod_statements[0]);
                eprintln!("POD 1 stmt indices: {:?}", out.pod_statements[1]);
                let total_placed: usize = out.pod_statements.iter().map(|v| v.len()).sum();
                assert_eq!(total_placed, shape.num_statements());
                assert_eq!(
                    out.pod_count, 13,
                    "expected 13 PODs under the per-POD publish cap with \
                     coupling-aware bin-packing and dynamic export \
                     tracking; MILP+cap optimum is 12"
                );
                let breakdown_for_check =
                    diagnostics::SolutionBreakdown::from_solution(&shape, &out);
                for pod in &breakdown_for_check.pods {
                    assert!(
                        pod.publishes.used <= shape.params.max_public_statements,
                        "POD {} publishes {} > max_public_statements ({})",
                        pod.pod_idx,
                        pod.publishes.used,
                        shape.params.max_public_statements
                    );
                }

                // Probe whether the DP layer beats greedy on bin-packing's
                // ordering. Under dynamic export tracking, bin-packing
                // builds segments large enough that greedy cuts can no
                // longer hit the DP's optimum on this ordering: greedy
                // returns K=14, DP returns K=13. Pinned so any future
                // shift back to parity is visible.
                let identity: Vec<usize> = (0..shape.num_statements()).collect();
                let bp_ordering =
                    partition::kahn_bin_packing(&shape, &identity).expect("DAG must be acyclic");
                let k_greedy = partition::simulate_greedy_k(&shape, &bp_ordering)
                    .expect("greedy partition must be feasible on bin-packing's ordering");
                let k_dp = partition::partition_with_ordering(&shape, &bp_ordering)
                    .expect("DP must find a feasible partition on bin-packing's ordering")
                    .pod_count;
                eprintln!(
                    "K_bp_greedy={} K_bp_dp={} on bin-packing's ordering",
                    k_greedy, k_dp
                );
                assert!(
                    k_dp <= k_greedy,
                    "DP must be at least as good as greedy on a fixed ordering"
                );
                assert_eq!(k_greedy, 14, "greedy on bin-packing's ordering pins at 14");
                assert_eq!(k_dp, 13, "DP on bin-packing's ordering pins at 13");

                // Probe the DFS-from-sinks ordering's K directly.
                let dfs_ordering = partition::build_dfs_topo_order(&shape);
                let k_dfs = partition::partition_with_ordering(&shape, &dfs_ordering)
                    .expect("DP must find a feasible partition on the DFS ordering")
                    .pod_count;
                eprintln!("K_dfs_dp={} on DFS-from-sinks ordering", k_dfs);
            }
            None => {
                let diag = diagnostics::diagnose_failure(&shape);
                panic!(
                    "partition() returned None; diagnosis: {}",
                    diag.as_ref()
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "None".to_string())
                );
            }
        }
    }

    /// Probe: what is MILP's K on cracked-refinery under the current
    /// caps? Last measured under statement-table accounting: K=11
    /// infeasible, K=12 feasible — so MILP optimum is K=12, unchanged
    /// from before the accounting fix. `#[ignore]`d because SCIP takes
    /// ~23s. Kept as a regression check: if the fixture or caps change,
    /// re-running this probe re-establishes the optimum so any new
    /// heuristic gap can be measured against it.
    #[test]
    #[ignore]
    fn cracked_refinery_fixture_milp() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        for k in [11, 12] {
            let out = partition_milp::solve_for_k(&shape, k);
            match out {
                Some(o) => eprintln!(
                    "MILP K={}: feasible, sizes={:?}",
                    k,
                    o.pod_statements.iter().map(|v| v.len()).collect::<Vec<_>>()
                ),
                None => eprintln!("MILP K={}: no solution (infeasible or timed out)", k),
            }
        }
    }

    /// Probe: what is the MILP-optimal K under the per-POD publish cap
    /// (`params.max_public_statements = 20`)? Settles whether the cap
    /// forces K higher than the unbounded MILP optimum (K=12) or whether
    /// the cap is "free" given a cap-aware partition. Iterates K from
    /// the unbounded optimum upward; first feasible K is the cap-bound
    /// optimum. `#[ignore]`'d because each `solve_for_k` invocation runs
    /// SCIP; the publish-cap formulation adds `n + n*k` binaries plus
    /// linking constraints, so wall-clock per call is higher than the
    /// vanilla MILP.
    #[test]
    #[ignore]
    fn cracked_refinery_fixture_milp_publish_cap() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        assert_eq!(shape.params.max_public_statements, 20);
        for k in [11, 12, 13, 14, 15, 16] {
            let out = partition_milp::solve_for_k_with_publish_cap(&shape, k);
            match out {
                Some(o) => {
                    let sizes: Vec<usize> =
                        o.pod_statements.iter().map(|v| v.len()).collect();
                    let breakdown = diagnostics::SolutionBreakdown::from_solution(&shape, &o);
                    let max_pubs = breakdown
                        .pods
                        .iter()
                        .map(|p| p.publishes.used)
                        .max()
                        .unwrap_or(0);
                    eprintln!(
                        "MILP+cap K={}: feasible, max publishes={}, sizes={:?}",
                        k, max_pubs, sizes
                    );
                    break;
                }
                None => eprintln!(
                    "MILP+cap K={}: no solution (infeasible or timed out)",
                    k
                ),
            }
        }
    }

    /// Probe: side-by-side per-statement diff between the heuristic
    /// partition and an MILP+cap K=12 partition. Surfaces (a) which
    /// statements end up in different relative positions, (b) what role
    /// distribution each MILP POD has (CPV head/sigverify/contains/etc.)
    /// versus each heuristic POD, and (c) how concentrated custom-predicate
    /// batch IDs are within each MILP POD. The goal is to spot structural
    /// patterns MILP exploits that the heuristic doesn't — candidate
    /// tiebreaks for an export-aware ordering generator. `#[ignore]`'d
    /// because it calls SCIP for the MILP partition.
    #[test]
    #[ignore]
    fn cracked_refinery_milp_vs_heuristic_diff() {
        use std::collections::HashMap;

        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");

        let heur_out =
            partition::partition(&shape).expect("heuristic must find a partition");
        let milp_out = partition_milp::solve_for_k_with_publish_cap(&shape, 12)
            .expect("MILP+cap must find K=12 on cracked-refinery");

        let n = shape.num_statements();
        let mut heur_pod = vec![usize::MAX; n];
        for (p, stmts) in heur_out.pod_statements.iter().enumerate() {
            for &s in stmts {
                heur_pod[s] = p;
            }
        }
        let mut milp_pod = vec![usize::MAX; n];
        for (p, stmts) in milp_out.pod_statements.iter().enumerate() {
            for &s in stmts {
                milp_pod[s] = p;
            }
        }

        let output_pub_set: std::collections::BTreeSet<usize> =
            shape.output_public_indices.iter().copied().collect();
        let consumers = shape.consumers();

        let role_of = |s: usize| -> &'static str {
            let c = &shape.costs[s];
            if c.custom_pred_verifications > 0 {
                "cpv_head"
            } else if c.signed_by > 0 {
                "signed_by"
            } else if c.public_key_of > 0 {
                "public_key_of"
            } else if c.merkle_state_transitions_small + c.merkle_state_transitions_medium > 0 {
                "merkle_trans"
            } else if c.merkle_proofs_small + c.merkle_proofs_medium > 0 {
                "merkle_proof"
            } else {
                "other"
            }
        };

        let print_pod_roles = |label: &str, pod_of: &[usize], pod_count: usize| {
            eprintln!("\n=== {} per-POD role distribution ===", label);
            for p in 0..pod_count {
                let mut role_counts: HashMap<&str, usize> = HashMap::new();
                let mut batches: std::collections::BTreeSet<_> =
                    std::collections::BTreeSet::new();
                for s in 0..n {
                    if pod_of[s] == p {
                        *role_counts.entry(role_of(s)).or_insert(0) += 1;
                        for id in &shape.costs[s].custom_predicates_ids {
                            batches.insert(id.clone());
                        }
                    }
                }
                let mut roles: Vec<(&str, usize)> = role_counts.into_iter().collect();
                roles.sort_by(|a, b| b.1.cmp(&a.1));
                let role_str: Vec<String> =
                    roles.iter().map(|(r, c)| format!("{}={}", r, c)).collect();
                eprintln!(
                    "  POD {:2}: distinct_batches={}, {}",
                    p,
                    batches.len(),
                    role_str.join(", ")
                );
            }
        };
        print_pod_roles("heuristic", &heur_pod, heur_out.pod_count);
        print_pod_roles("MILP+cap", &milp_pod, milp_out.pod_count);

        // Statements where MILP's relative POD position differs
        // substantially from the heuristic's. Normalize POD index to
        // [0, 1] in each partition so K-difference doesn't bias the
        // comparison.
        let to_fraction = |p: usize, total: usize| {
            if total <= 1 {
                0.0
            } else {
                p as f64 / (total - 1) as f64
            }
        };
        let mut movers: Vec<(usize, f64)> = (0..n)
            .filter_map(|s| {
                let h = to_fraction(heur_pod[s], heur_out.pod_count);
                let m = to_fraction(milp_pod[s], milp_out.pod_count);
                let delta = (h - m).abs();
                (delta > 0.20).then_some((s, delta))
            })
            .collect();
        movers.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        eprintln!(
            "\n=== {} of {} statements moved >0.20 in normalized POD position ===",
            movers.len(),
            n
        );
        for (s, delta) in movers.iter().take(20) {
            eprintln!(
                "  stmt {:3}: heur POD {:2} -> MILP POD {:2}, delta={:.2}, role={}",
                s,
                heur_pod[*s],
                milp_pod[*s],
                delta,
                role_of(*s)
            );
        }

        // Raw CSV dump for offline analysis. One line per statement.
        eprintln!("\n=== per-statement table ===");
        eprintln!("stmt,heur_pod,milp_pod,role,n_consumers,n_batches,is_out_pub");
        for s in 0..n {
            eprintln!(
                "{},{},{},{},{},{},{}",
                s,
                heur_pod[s],
                milp_pod[s],
                role_of(s),
                consumers[s].len(),
                shape.costs[s].custom_predicates_ids.len(),
                output_pub_set.contains(&s),
            );
        }
    }

    /// Probe: MILP+cap K=12 partition stability across SCIP random
    /// seeds. Runs two MILP solves at K=12 with different
    /// `randomization/randomseedshift` values, then asks: of the per-pair
    /// co-locations that hold in partition A, how many hold in partition
    /// B? Pairs stable across seeds are structurally required by the
    /// problem; pairs that flip are incidental to SCIP's solver path.
    /// Stable pairs are the candidates a smarter heuristic would need to
    /// co-locate; unstable pairs aren't worth chasing. Also checks
    /// where the top mover clusters from
    /// `cracked_refinery_milp_vs_heuristic_diff` (stmts 17-21, 181-185,
    /// 215-218, 220-221, 246, 337) land in each partition — if the same
    /// cluster lands together in both, that's a structural co-location;
    /// if it scatters, the heuristic-vs-MILP delta on that cluster was
    /// just one of several equally-good MILP placements.
    /// `#[ignore]`'d because it runs MILP twice (~160s).
    #[test]
    #[ignore]
    /// Dump per-statement structural info (cost vector, role, dep
    /// edges in both directions, custom predicate IDs) for the
    /// MILP-stable violator clusters surfaced by
    /// `cracked_refinery_milp_multi_seed_pair_stability`. Pure
    /// fixture introspection — no SCIP — but `#[ignore]`'d to keep
    /// the default test run quiet.
    #[test]
    #[ignore]
    fn cracked_refinery_violator_content() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let consumers = shape.consumers();

        let role_of = |s: usize| -> &'static str {
            let c = &shape.costs[s];
            if c.custom_pred_verifications > 0 {
                "cpv_head"
            } else if c.signed_by > 0 {
                "signed_by"
            } else if c.public_key_of > 0 {
                "public_key_of"
            } else if c.merkle_state_transitions_small + c.merkle_state_transitions_medium > 0 {
                "merkle_trans"
            } else if c.merkle_proofs_small + c.merkle_proofs_medium > 0 {
                "merkle_proof"
            } else {
                "other"
            }
        };

        let dump = |s: usize| {
            let c = &shape.costs[s];
            eprintln!("  stmt {} (role={}):", s, role_of(s));
            eprintln!(
                "    costs: merkle_proofs(s={}, m={}), state_trans(s={}, m={}), cpv={}, signed_by={}, pko={}, n_predicates={}",
                c.merkle_proofs_small,
                c.merkle_proofs_medium,
                c.merkle_state_transitions_small,
                c.merkle_state_transitions_medium,
                c.custom_pred_verifications,
                c.signed_by,
                c.public_key_of,
                c.custom_predicates_ids.len(),
            );
            // Stable, short-form custom predicate IDs (hex prefix).
            let cps: Vec<String> = c
                .custom_predicates_ids
                .iter()
                .map(|id| format!("{:?}", id))
                .collect();
            for cp in &cps {
                eprintln!("    predicate: {}", cp);
            }
            let mut deps_internal: Vec<usize> = Vec::new();
            let mut deps_external: Vec<(usize, usize)> = Vec::new();
            for dep in &shape.dep_edges[s] {
                match dep {
                    AbstractDep::Internal(d) => deps_internal.push(*d),
                    AbstractDep::External { pod, statement } => {
                        deps_external.push((*pod, *statement))
                    }
                }
            }
            deps_internal.sort();
            deps_internal.dedup();
            eprintln!(
                "    consumes (Internal): {:?}",
                deps_internal
                    .iter()
                    .map(|d| (*d, role_of(*d)))
                    .collect::<Vec<_>>()
            );
            if !deps_external.is_empty() {
                eprintln!("    consumes (External): {:?}", deps_external);
            }
            let mut conss: Vec<usize> = consumers[s].clone();
            conss.sort();
            conss.dedup();
            eprintln!(
                "    consumed by: {:?}",
                conss
                    .iter()
                    .map(|c| (*c, role_of(*c)))
                    .collect::<Vec<_>>()
            );
        };

        eprintln!("=== Cluster A (split POD 1/2 in old K=14 partition) ===");
        for &s in &[24, 25, 34, 35, 36, 37] {
            dump(s);
        }
        eprintln!("\n=== Cluster B (scattered in old K=14 partition) ===");
        for &s in &[117, 118, 124, 136, 137, 160, 161, 216] {
            dump(s);
        }
    }

    fn cracked_refinery_milp_seed_stability() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");

        let seed_a = 0_i32;
        let seed_b = 42_i32;
        let out_a = partition_milp::solve_for_k_with_publish_cap_seed(&shape, 12, seed_a)
            .expect("MILP+cap seed=0 must find K=12");
        let out_b = partition_milp::solve_for_k_with_publish_cap_seed(&shape, 12, seed_b)
            .expect("MILP+cap seed=42 must find K=12");

        let n = shape.num_statements();
        let mut pod_a = vec![usize::MAX; n];
        let mut pod_b = vec![usize::MAX; n];
        for (p, stmts) in out_a.pod_statements.iter().enumerate() {
            for &s in stmts {
                pod_a[s] = p;
            }
        }
        for (p, stmts) in out_b.pod_statements.iter().enumerate() {
            for &s in stmts {
                pod_b[s] = p;
            }
        }

        // Pairwise co-location stability.
        let mut pairs_a = 0_usize;
        let mut pairs_b = 0_usize;
        let mut pairs_both = 0_usize;
        let mut pairs_only_a = 0_usize;
        let mut pairs_only_b = 0_usize;
        for i in 0..n {
            for j in (i + 1)..n {
                let same_a = pod_a[i] == pod_a[j];
                let same_b = pod_b[i] == pod_b[j];
                match (same_a, same_b) {
                    (true, true) => {
                        pairs_a += 1;
                        pairs_b += 1;
                        pairs_both += 1;
                    }
                    (true, false) => {
                        pairs_a += 1;
                        pairs_only_a += 1;
                    }
                    (false, true) => {
                        pairs_b += 1;
                        pairs_only_b += 1;
                    }
                    (false, false) => {}
                }
            }
        }
        let stable_pct = if pairs_a == 0 {
            0.0
        } else {
            100.0 * pairs_both as f64 / pairs_a as f64
        };
        eprintln!(
            "Co-location pairs: A={}, B={}, in both={} ({:.1}% of A), only A={}, only B={}",
            pairs_a, pairs_b, pairs_both, stable_pct, pairs_only_a, pairs_only_b
        );

        // Track the mover clusters identified by the previous diff probe.
        let clusters: &[&[usize]] = &[
            &[17, 18, 19, 20, 21],
            &[181, 184, 185],
            &[215, 216, 217, 218],
            &[220, 221],
            &[160, 161],
            &[246],
            &[337],
        ];
        eprintln!("\n=== mover-cluster placements across seeds ===");
        for cluster in clusters {
            let pods_a: Vec<usize> = cluster.iter().map(|&s| pod_a[s]).collect();
            let pods_b: Vec<usize> = cluster.iter().map(|&s| pod_b[s]).collect();
            let all_same_a = pods_a.windows(2).all(|w| w[0] == w[1]);
            let all_same_b = pods_b.windows(2).all(|w| w[0] == w[1]);
            eprintln!(
                "  cluster {:?}: A={:?} (co-located={}), B={:?} (co-located={})",
                cluster, pods_a, all_same_a, pods_b, all_same_b
            );
        }
    }

    /// Probe: across multiple SCIP random seeds, which statement pairs
    /// are consistently co-located in MILP+cap K=12 partitions? The
    /// stable-pair set is the structural co-location signal — pairs MILP
    /// always groups are dependency-coupled clusters the heuristic
    /// should respect, while pairs that flip across seeds are incidental.
    /// Compares the stable set against the production heuristic's K=14
    /// partition and reports how many stable pairs the heuristic
    /// violates and which statements account for the most violations.
    /// `#[ignore]`'d because it runs MILP `seeds.len()` times (~7 min
    /// for 5 seeds).
    #[test]
    #[ignore]
    fn cracked_refinery_milp_multi_seed_pair_stability() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let n = shape.num_statements();

        let seeds = [0_i32, 17, 42, 101, 999];
        let m = seeds.len();
        let mut partitions: Vec<Vec<usize>> = Vec::new();
        for (i, &seed) in seeds.iter().enumerate() {
            let out = partition_milp::solve_for_k_with_publish_cap_seed(&shape, 12, seed)
                .unwrap_or_else(|| {
                    panic!("MILP+cap seed={} run {}/{} must find K=12", seed, i + 1, m)
                });
            let mut pod_of = vec![usize::MAX; n];
            for (p, stmts) in out.pod_statements.iter().enumerate() {
                for &s in stmts {
                    pod_of[s] = p;
                }
            }
            eprintln!(
                "MILP seed={} K=12: sizes={:?}",
                seed,
                out.pod_statements.iter().map(|v| v.len()).collect::<Vec<_>>()
            );
            partitions.push(pod_of);
        }

        // Pair co-location frequency: for each ordered pair (i, j) with
        // i < j, count how many of the `m` seeds put them in the same
        // POD. Distribution shows how much of the partition is
        // structurally forced vs solver-incidental.
        let mut freq_hist = vec![0_usize; m + 1];
        let mut stable_pairs: Vec<(usize, usize)> = Vec::new();
        let stable_threshold = m; // require unanimous co-location
        for i in 0..n {
            for j in (i + 1)..n {
                let count = partitions.iter().filter(|p| p[i] == p[j]).count();
                freq_hist[count] += 1;
                if count >= stable_threshold {
                    stable_pairs.push((i, j));
                }
            }
        }
        let total_pairs: usize = freq_hist.iter().sum();
        eprintln!("\n=== Pair co-location frequency across {} seeds ===", m);
        for (freq, &count) in freq_hist.iter().enumerate() {
            eprintln!(
                "  same-POD in {}/{} seeds: {:>5} pairs ({:>5.1}%)",
                freq,
                m,
                count,
                100.0 * count as f64 / total_pairs as f64
            );
        }
        eprintln!(
            "\nStable pairs (same POD in all {} seeds): {}",
            m,
            stable_pairs.len()
        );

        // How many stable pairs does the production heuristic respect?
        let heur_out = partition::partition(&shape).expect("heuristic must find a partition");
        let mut heur_pod = vec![usize::MAX; n];
        for (p, stmts) in heur_out.pod_statements.iter().enumerate() {
            for &s in stmts {
                heur_pod[s] = p;
            }
        }
        let respected: usize = stable_pairs
            .iter()
            .filter(|&&(i, j)| heur_pod[i] == heur_pod[j])
            .count();
        let violated = stable_pairs.len() - respected;
        let respect_pct = if stable_pairs.is_empty() {
            0.0
        } else {
            100.0 * respected as f64 / stable_pairs.len() as f64
        };
        eprintln!(
            "\nProduction heuristic (K={}) respects {}/{} stable pairs ({:.1}%), violates {}",
            heur_out.pod_count,
            respected,
            stable_pairs.len(),
            respect_pct,
            violated,
        );

        // Which statements account for the most violations? A stmt with
        // many violated stable-partners is one the heuristic has split
        // away from its structurally-required cluster.
        let mut violations_per_stmt = vec![0_usize; n];
        for &(i, j) in &stable_pairs {
            if heur_pod[i] != heur_pod[j] {
                violations_per_stmt[i] += 1;
                violations_per_stmt[j] += 1;
            }
        }
        let mut ranked: Vec<(usize, usize)> = (0..n)
            .filter(|&s| violations_per_stmt[s] > 0)
            .map(|s| (s, violations_per_stmt[s]))
            .collect();
        ranked.sort_by_key(|&(_, c)| std::cmp::Reverse(c));
        eprintln!(
            "\n=== Top 20 statements by violated stable-pair count (heur POD shown) ==="
        );
        for (s, c) in ranked.iter().take(20) {
            eprintln!(
                "  stmt {:3}: {:2} violations, heur POD {:2}",
                s, c, heur_pod[*s]
            );
        }

        // Drill-down on violator structure: roles, dep relationships,
        // shared batches. Surfaces whether violators are e.g. CPV
        // body+head pairs the heuristic split, or unrelated statements
        // that just happen to co-locate in MILP.
        let role_of = |s: usize| -> &'static str {
            let c = &shape.costs[s];
            if c.custom_pred_verifications > 0 {
                "cpv_head"
            } else if c.signed_by > 0 {
                "signed_by"
            } else if c.public_key_of > 0 {
                "public_key_of"
            } else if c.merkle_state_transitions_small + c.merkle_state_transitions_medium > 0 {
                "merkle_trans"
            } else if c.merkle_proofs_small + c.merkle_proofs_medium > 0 {
                "merkle_proof"
            } else {
                "other"
            }
        };
        let dep_rel = |a: usize, b: usize| -> &'static str {
            let a_uses_b = shape.dep_edges[a].iter().any(
                |d| matches!(d, AbstractDep::Internal(x) if *x == b),
            );
            let b_uses_a = shape.dep_edges[b].iter().any(
                |d| matches!(d, AbstractDep::Internal(x) if *x == a),
            );
            match (a_uses_b, b_uses_a) {
                (true, _) => "a_consumes_b",
                (_, true) => "b_consumes_a",
                _ => "sibling",
            }
        };
        let shared_batches = |a: usize, b: usize| -> usize {
            let ids_a: std::collections::BTreeSet<_> =
                shape.costs[a].custom_predicates_ids.iter().collect();
            let ids_b: std::collections::BTreeSet<_> =
                shape.costs[b].custom_predicates_ids.iter().collect();
            ids_a.intersection(&ids_b).count()
        };

        eprintln!("\n=== Violator drill-down (per top-10 violator) ===");
        for (s, _) in ranked.iter().take(10) {
            let partners: Vec<usize> = stable_pairs
                .iter()
                .filter_map(|&(i, j)| {
                    if i == *s {
                        Some(j)
                    } else if j == *s {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect();
            let violated: Vec<usize> = partners
                .iter()
                .copied()
                .filter(|&p| heur_pod[p] != heur_pod[*s])
                .collect();
            let respected: Vec<usize> = partners
                .iter()
                .copied()
                .filter(|&p| heur_pod[p] == heur_pod[*s])
                .collect();
            eprintln!(
                "  stmt {} (heur POD {}, role={}): {} stable partners, {} respected, {} violated",
                s,
                heur_pod[*s],
                role_of(*s),
                partners.len(),
                respected.len(),
                violated.len()
            );
            for v in violated {
                eprintln!(
                    "    -> stmt {} (heur POD {}, role={}, rel={}, shared_batches={})",
                    v,
                    heur_pod[v],
                    role_of(v),
                    dep_rel(*s, v),
                    shared_batches(*s, v)
                );
            }
        }

        // Where do violation splits land (which POD pairs)? Surfaces
        // whether violators are predominantly adjacent-POD splits
        // (cluster sliced across a single cut) or long-range splits
        // (genuine global rearrangement).
        let mut split_dist = vec![0_usize; heur_out.pod_count];
        let mut split_pairs: std::collections::HashMap<(usize, usize), usize> =
            std::collections::HashMap::new();
        for &(i, j) in &stable_pairs {
            if heur_pod[i] != heur_pod[j] {
                let lo = heur_pod[i].min(heur_pod[j]);
                let hi = heur_pod[i].max(heur_pod[j]);
                split_dist[hi - lo] += 1;
                *split_pairs.entry((lo, hi)).or_insert(0) += 1;
            }
        }
        eprintln!("\n=== Violation distance histogram (heur POD chain distance) ===");
        for (d, c) in split_dist.iter().enumerate().filter(|(_, &c)| c > 0) {
            eprintln!("  distance {}: {} violations", d, c);
        }
        eprintln!("\n=== Top 10 violation-emitting POD pairs ===");
        let mut splits_ranked: Vec<_> = split_pairs.into_iter().collect();
        splits_ranked.sort_by_key(|&(_, c)| std::cmp::Reverse(c));
        for ((p1, p2), c) in splits_ranked.iter().take(10) {
            eprintln!("  ({:2}, {:2}): {} pairs (distance {})", p1, p2, c, p2 - p1);
        }
    }

    /// Probe: can the cap-aware DP reach K=12 on cracked-refinery if we
    /// feed it an ordering derived from MILP's cap-aware K=12 partition?
    /// Builds an ordering by sorting statements by (pod_index in MILP's
    /// solution, position in a baseline topo sort) so each MILP POD is a
    /// contiguous block. Three possible outcomes carry distinct
    /// implications:
    /// - DP returns K=12: the gap is purely in the ordering generator.
    ///   Pull MILP's ordering shape into the candidate set (or learn
    ///   a heuristic that produces it).
    /// - DP returns K=14: the DP itself can't reach K=12 even from the
    ///   right ordering. Suggests the segment-feasibility check or the
    ///   prefix-DP search depth is the bottleneck, not generation.
    /// - DP returns K=13: both layers contribute partially.
    /// `#[ignore]`'d because it calls SCIP.
    #[test]
    #[ignore]
    fn cracked_refinery_milp_ordering_probe() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let milp_out = partition_milp::solve_for_k_with_publish_cap(&shape, 12)
            .expect("MILP+cap must find K=12 (regression in fixture or formulation otherwise)");

        let n = shape.num_statements();
        let mut pod_of: Vec<usize> = vec![usize::MAX; n];
        for (p, stmts) in milp_out.pod_statements.iter().enumerate() {
            for &s in stmts {
                pod_of[s] = p;
            }
        }

        // Baseline global topo order. Within each MILP POD, we'll keep
        // statements in this order; across PODs, the lower POD index
        // comes first. The MILP's topo precedence constraint guarantees
        // this concatenation is itself a valid topological ordering.
        let identity_priority: Vec<usize> = (0..n).collect();
        let global_topo = partition::kahn_with_priority(&shape, &identity_priority)
            .expect("statement DAG must be acyclic");
        let mut pos_in_global = vec![0_usize; n];
        for (i, &s) in global_topo.iter().enumerate() {
            pos_in_global[s] = i;
        }

        let mut ordering: Vec<usize> = (0..n).collect();
        ordering.sort_by_key(|&s| (pod_of[s], pos_in_global[s]));

        let dp_out = partition::partition_with_ordering(&shape, &ordering)
            .expect("DP must produce a partition on a valid topo ordering");

        eprintln!(
            "MILP+cap-derived ordering: DP returns K={}, sizes={:?}",
            dp_out.pod_count,
            dp_out
                .pod_statements
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>()
        );

        let prod_out = partition::partition(&shape).expect("production partition");
        eprintln!("production K = {}", prod_out.pod_count);

        assert!(
            dp_out.pod_count <= prod_out.pod_count,
            "DP on MILP-derived ordering must be at least as good as the production heuristic; \
             got K={} vs production K={}",
            dp_out.pod_count,
            prod_out.pod_count,
        );
    }

    /// Cross-reference: where do heuristic's POD 3 statements (the
    /// stmt-saturated, CPV-light cluster suspected to drive the K=13/K=12
    /// gap) end up in MILP's K=12 partition? If MILP spreads them across
    /// many PODs, the "import-heavy cluster needs to be split" hypothesis
    /// holds; if MILP also keeps them together, the gap is elsewhere.
    /// `#[ignore]`'d (calls SCIP).
    #[test]
    #[ignore]
    fn cracked_refinery_pod3_dispersion() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let n = shape.num_statements();

        let heur = partition::partition(&shape).expect("heuristic partitions");
        assert_eq!(heur.pod_count, 13);
        let heur_pod3: Vec<usize> = heur.pod_statements[3].clone();
        eprintln!("Heuristic POD 3: {} statements", heur_pod3.len());

        let milp_out = partition_milp::solve_for_k(&shape, 12).expect("MILP must find K=12");
        let mut milp_of: Vec<usize> = vec![usize::MAX; n];
        for (p, stmts) in milp_out.pod_statements.iter().enumerate() {
            for &s in stmts {
                milp_of[s] = p;
            }
        }

        let mut dispersion: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        for &s in &heur_pod3 {
            *dispersion.entry(milp_of[s]).or_insert(0) += 1;
        }
        eprintln!(
            "  Their MILP POD distribution (milp_pod -> count): {:?}",
            dispersion
        );

        // Also compute per-MILP-POD CPV totals to see how MILP balances.
        eprintln!("\nMILP POD CPV totals:");
        for (p, stmts) in milp_out.pod_statements.iter().enumerate() {
            let cpv: usize = stmts
                .iter()
                .map(|&s| shape.costs[s].custom_pred_verifications)
                .sum();
            let n_stmts = stmts.len();
            eprintln!("  POD {}: {} stmts, {} CPV", p, n_stmts, cpv);
        }

        // For comparison, heuristic CPV per POD.
        eprintln!("\nHeuristic POD CPV totals:");
        for (p, stmts) in heur.pod_statements.iter().enumerate() {
            let cpv: usize = stmts
                .iter()
                .map(|&s| shape.costs[s].custom_pred_verifications)
                .sum();
            let n_stmts = stmts.len();
            eprintln!("  POD {}: {} stmts, {} CPV", p, n_stmts, cpv);
        }
    }

    /// Detailed partition-diff between heuristic K=13 and MILP K=12 for
    /// cracked-refinery. Prints (1) the transfer matrix of statements,
    /// (2) which heuristic POD is "dissolved" in MILP's solution, (3) for
    /// each scattered statement, its heuristic ordering position and MILP
    /// target POD, and (4) the heuristic-vs-MILP ordering positions to
    /// gauge how far the heuristic ordering is from MILP's effective one.
    /// `#[ignore]`'d (calls SCIP).
    #[test]
    #[ignore]
    fn cracked_refinery_partition_diff() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let n = shape.num_statements();

        // Heuristic K=13 + its ordering. Run bin-packing directly so we can
        // pin the ordering it was generated from for position-by-position
        // comparison.
        let identity: Vec<usize> = (0..n).collect();
        let bp_ordering = partition::kahn_bin_packing(&shape, &identity)
            .expect("bin-packing must produce an ordering");
        let heur = partition::partition_with_ordering(&shape, &bp_ordering)
            .expect("DP must produce a partition on bin-packing ordering");
        assert_eq!(heur.pod_count, 13);
        let mut heur_pod_of: Vec<usize> = vec![usize::MAX; n];
        for (p, stmts) in heur.pod_statements.iter().enumerate() {
            for &s in stmts {
                heur_pod_of[s] = p;
            }
        }
        let mut heur_pos: Vec<usize> = vec![usize::MAX; n];
        for (i, &s) in bp_ordering.iter().enumerate() {
            heur_pos[s] = i;
        }

        // MILP K=12 partition.
        let milp = partition_milp::solve_for_k(&shape, 12).expect("MILP K=12 must be feasible");
        let mut milp_pod_of: Vec<usize> = vec![usize::MAX; n];
        for (p, stmts) in milp.pod_statements.iter().enumerate() {
            for &s in stmts {
                milp_pod_of[s] = p;
            }
        }

        // Transfer matrix: rows = MILP POD, cols = heur POD.
        let mut transfer = vec![vec![0_usize; 13]; 12];
        for s in 0..n {
            transfer[milp_pod_of[s]][heur_pod_of[s]] += 1;
        }
        eprintln!("Transfer matrix (rows=MILP POD, cols=heur POD):");
        eprint!("            ");
        for q in 0..13 {
            eprint!("h{:<3} ", q);
        }
        eprintln!();
        for (p, row) in transfer.iter().enumerate() {
            eprint!("  MILP{:2}:  ", p);
            for &v in row.iter() {
                if v == 0 {
                    eprint!("   . ");
                } else {
                    eprint!("{:4} ", v);
                }
            }
            let total: usize = row.iter().sum();
            eprintln!(" (total {})", total);
        }

        // Greedy max-overlap matching: for each MILP POD, find best
        // heuristic POD. The unmatched heuristic POD is the "dissolved" one.
        let mut milp_match = [usize::MAX; 12];
        let mut used = [false; 13];
        let mut pairs: Vec<(usize, usize, usize)> = Vec::new();
        for (p, row) in transfer.iter().enumerate() {
            for (q, &v) in row.iter().enumerate() {
                pairs.push((v, p, q));
            }
        }
        pairs.sort_by(|a, b| b.0.cmp(&a.0));
        for (_, p, q) in pairs {
            if milp_match[p] == usize::MAX && !used[q] {
                milp_match[p] = q;
                used[q] = true;
            }
        }
        let dissolved: Vec<usize> = (0..13).filter(|&q| !used[q]).collect();
        eprintln!("MILP POD -> best-matching heur POD:");
        for p in 0..12 {
            let q = milp_match[p];
            let kept = transfer[p][q];
            let total: usize = transfer[p].iter().sum();
            eprintln!(
                "  MILP{:2} -> heur{:2}  ({} of {} kept; {} migrated in)",
                p,
                q,
                kept,
                total,
                total - kept
            );
        }
        eprintln!("Dissolved heuristic PODs: {:?}", dissolved);

        // Heuristic-POD-CPV vs MILP-POD-CPV (for context).
        eprintln!("\nHeur POD CPV/stmt counts:");
        for p in 0..13 {
            let stmts = &heur.pod_statements[p];
            let cpv: usize = stmts
                .iter()
                .map(|&s| shape.costs[s].custom_pred_verifications)
                .sum();
            eprintln!("  heur{:2}: {:2} stmts, {} CPV", p, stmts.len(), cpv);
        }
        eprintln!("MILP POD CPV/stmt counts:");
        for p in 0..12 {
            let stmts = &milp.pod_statements[p];
            let cpv: usize = stmts
                .iter()
                .map(|&s| shape.costs[s].custom_pred_verifications)
                .sum();
            eprintln!("  MILP{:2}: {:2} stmts, {} CPV", p, stmts.len(), cpv);
        }

        // Construct a MILP-derived ordering: concatenate statements by
        // (milp_pod_of, topo_pos). Use bp_ordering's position as the
        // intra-POD topo order; it's a valid topo sort and stable.
        let mut milp_ordering: Vec<usize> = (0..n).collect();
        milp_ordering.sort_by_key(|&s| (milp_pod_of[s], heur_pos[s]));
        let mut milp_pos: Vec<usize> = vec![usize::MAX; n];
        for (i, &s) in milp_ordering.iter().enumerate() {
            milp_pos[s] = i;
        }

        // Sanity check: is the MILP-derived ordering itself a valid topo
        // ordering? (MILP's pod-precedence + bp_ordering tiebreak should
        // give a valid one, but verify.)
        let mut topo_valid = true;
        for s in 0..n {
            for dep in &shape.dep_edges[s] {
                if let AbstractDep::Internal(d) = dep {
                    if milp_pos[*d] >= milp_pos[s] {
                        topo_valid = false;
                        break;
                    }
                }
            }
            if !topo_valid {
                break;
            }
        }
        eprintln!("\nMILP-derived ordering is topo-valid: {}", topo_valid);

        // DP K on the MILP-derived ordering.
        if topo_valid {
            let milp_dp = partition::partition_with_ordering(&shape, &milp_ordering);
            eprintln!(
                "DP K on MILP-derived ordering: {:?}",
                milp_dp.as_ref().map(|o| o.pod_count)
            );
        }

        // Position diff distribution: how far does each statement move
        // between bp_ordering and milp_ordering?
        let mut diffs: Vec<i64> = (0..n)
            .map(|s| milp_pos[s] as i64 - heur_pos[s] as i64)
            .collect();
        let absdiffs: Vec<i64> = diffs.iter().map(|d| d.abs()).collect();
        let max_diff = absdiffs.iter().copied().max().unwrap_or(0);
        let mean_diff = absdiffs.iter().sum::<i64>() as f64 / n as f64;
        let unchanged = diffs.iter().filter(|&&d| d == 0).count();
        let small_move = diffs.iter().filter(|&&d| d.abs() <= 5 && d != 0).count();
        let medium_move = diffs
            .iter()
            .filter(|&&d| d.abs() > 5 && d.abs() <= 50)
            .count();
        let large_move = diffs.iter().filter(|&&d| d.abs() > 50).count();
        eprintln!(
            "Position diff bp->milp: max={} mean={:.1} | unchanged={} small(<=5)={} medium(6-50)={} large(>50)={}",
            max_diff, mean_diff, unchanged, small_move, medium_move, large_move
        );

        // Kendall tau (number of pairwise inversions) is too expensive at
        // n=345; report a sample-based proxy instead: how often does
        // (bp_ordering[i] < bp_ordering[j]) match
        // (milp_pos[bp_ordering[i]] < milp_pos[bp_ordering[j]])?
        let sample_pairs = 5000;
        let mut rng_state = 0xDEADBEEF_u64;
        let mut concord = 0;
        let mut discord = 0;
        for _ in 0..sample_pairs {
            rng_state = rng_state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let i = (rng_state >> 33) as usize % n;
            rng_state = rng_state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let j = (rng_state >> 33) as usize % n;
            if i == j {
                continue;
            }
            let s_i = bp_ordering[i.min(j)];
            let s_j = bp_ordering[i.max(j)];
            if milp_pos[s_i] < milp_pos[s_j] {
                concord += 1;
            } else {
                discord += 1;
            }
        }
        let total = concord + discord;
        eprintln!(
            "Pairwise concord (random {} pairs): {} concordant / {} = {:.1}%",
            total,
            concord,
            total,
            100.0 * concord as f64 / total as f64
        );
        diffs.sort();
        eprintln!(
            "Diff percentiles: p10={} p25={} p50={} p75={} p90={}",
            diffs[n * 10 / 100],
            diffs[n * 25 / 100],
            diffs[n * 50 / 100],
            diffs[n * 75 / 100],
            diffs[n * 90 / 100],
        );

        // Probe: how few statements need to be at their MILP position
        // (with the rest preserving bp_ordering's relative order) for
        // DP K to drop to 12? Largest movers first.
        let mut indices: Vec<usize> = (0..n).collect();
        indices
            .sort_by_key(|&s| std::cmp::Reverse((milp_pos[s] as i64 - heur_pos[s] as i64).abs()));
        eprintln!("\nGreedy 'minimum critical commits' probe:");
        eprintln!("  Commit top-K largest movers to their MILP positions; rest fill in bp_ordering order.");
        eprintln!("  {:<10} {:<10} {:<8}", "committed", "topo_ok", "dp_k");
        for k_commit in [0, 5, 10, 20, 40, 60, 80, 120, 160, 200, 240, 345] {
            let k_commit = k_commit.min(n);
            let committed: HashSet<usize> = indices.iter().take(k_commit).copied().collect();
            let mut slot: Vec<usize> = vec![usize::MAX; n];
            for &s in &committed {
                slot[milp_pos[s]] = s;
            }
            let remaining: Vec<usize> = bp_ordering
                .iter()
                .copied()
                .filter(|s| !committed.contains(s))
                .collect();
            let mut ri = 0;
            for s in slot.iter_mut() {
                if *s == usize::MAX {
                    *s = remaining[ri];
                    ri += 1;
                }
            }
            // Topo check.
            let mut pos_new = vec![0_usize; n];
            for (i, &s) in slot.iter().enumerate() {
                pos_new[s] = i;
            }
            let mut topo_ok = true;
            for s in 0..n {
                for dep in &shape.dep_edges[s] {
                    if let AbstractDep::Internal(d) = dep {
                        if pos_new[*d] >= pos_new[s] {
                            topo_ok = false;
                            break;
                        }
                    }
                }
                if !topo_ok {
                    break;
                }
            }
            let dp_k = if topo_ok {
                partition::partition_with_ordering(&shape, &slot).map(|o| o.pod_count)
            } else {
                None
            };
            eprintln!("  {:<10} {:<10} {:?}", k_commit, topo_ok, dp_k);
        }

        // List statements that move and where they go.
        let mut moves: Vec<(usize, usize, usize)> = Vec::new();
        for s in 0..n {
            let q = heur_pod_of[s];
            let p = milp_pod_of[s];
            let q_target_for_p = milp_match[p];
            if q != q_target_for_p {
                moves.push((s, q, p));
            }
        }
        eprintln!(
            "\nStatements moving across heur->MILP (relative to greedy POD match): {}",
            moves.len()
        );
        eprintln!("(stmt | heur_pod heur_pos | milp_pod milp_match | cpv | mp | mst | sb | cps)");
        for (s, heur_p, milp_p) in &moves {
            let c = &shape.costs[*s];
            eprintln!(
                "  s={:3} | heur{:2} pos {:3} | MILP{:2} (match heur{:2}) | cpv={} mp_s={} mp_m={} mst_s={} mst_m={} sb={} cps={}",
                s,
                heur_p,
                heur_pos[*s],
                milp_p,
                milp_match[*milp_p],
                c.custom_pred_verifications,
                c.merkle_proofs_small,
                c.merkle_proofs_medium,
                c.merkle_state_transitions_small,
                c.merkle_state_transitions_medium,
                c.signed_by,
                c.custom_predicates_ids.len(),
            );
        }
    }

    /// Probe: characterise cracked-refinery's CPV block structure. For
    /// each CPV head, count direct Internal deps that have no other
    /// consumers (the "exclusive body") and report the block-size
    /// histogram. Then estimate the minimum K achievable by atomic
    /// block packing (CPV head + body bundled inseparably) via
    /// first-fit-decreasing. Used to decide whether a pure block-based
    /// generator is viable for this fixture or whether atomic packing
    /// would regress.
    #[test]
    fn cracked_refinery_block_size_probe() {
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let n = shape.num_statements();

        // Inverse of dep_edges: for each statement, who depends on it.
        let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, edges) in shape.dep_edges.iter().enumerate() {
            for dep in edges {
                if let AbstractDep::Internal(d) = dep {
                    consumers[*d].push(i);
                }
            }
        }

        // For each CPV head, compute exclusive vs shared direct-body counts.
        let mut block_sizes: Vec<usize> = Vec::new();
        let mut cpv_count: usize = 0;
        let mut total_exclusive: usize = 0;
        let mut total_shared: usize = 0;
        let mut total_external_deps: usize = 0;
        for (i, cost) in shape.costs.iter().enumerate() {
            if cost.custom_pred_verifications == 0 {
                continue;
            }
            cpv_count += 1;
            let mut excl = 0;
            let mut shared = 0;
            let mut ext = 0;
            for dep in &shape.dep_edges[i] {
                match dep {
                    AbstractDep::Internal(d) => {
                        if consumers[*d].len() == 1 && consumers[*d][0] == i {
                            excl += 1;
                        } else {
                            shared += 1;
                        }
                    }
                    AbstractDep::External { .. } => ext += 1,
                }
            }
            block_sizes.push(1 + excl);
            total_exclusive += excl;
            total_shared += shared;
            total_external_deps += ext;
        }

        eprintln!("Total CPV heads: {}", cpv_count);
        eprintln!("Total exclusive direct body stmts: {}", total_exclusive);
        eprintln!("Total shared direct body stmts: {}", total_shared);
        eprintln!(
            "Total external direct deps on CPVs: {}",
            total_external_deps
        );
        let mean_block: f64 = block_sizes.iter().sum::<usize>() as f64 / cpv_count.max(1) as f64;
        eprintln!("Mean block size (head + exclusive body): {:.2}", mean_block);

        let mut hist: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
        for &sz in &block_sizes {
            *hist.entry(sz).or_insert(0) += 1;
        }
        eprintln!("Block-size histogram:");
        for (sz, count) in &hist {
            eprintln!("  size {:>2}: {:>3} blocks", sz, count);
        }

        // Estimate K under atomic block-based packing via FFD.
        // Caps: max_statements stmts/POD, max_custom_pred_verifications
        // CPVs/POD. Each block contributes block_size stmts and 1 CPV.
        let p = &shape.params;
        let max_stmts = p.max_statements;
        let max_cpvs = p.max_custom_predicate_verifications;
        let mut sorted = block_sizes.clone();
        sorted.sort_unstable();
        sorted.reverse();
        let mut bins: Vec<(usize, usize)> = Vec::new();
        for &b in &sorted {
            let mut placed = false;
            for bin in bins.iter_mut() {
                if bin.0 + b <= max_stmts && bin.1 < max_cpvs {
                    bin.0 += b;
                    bin.1 += 1;
                    placed = true;
                    break;
                }
            }
            if !placed {
                bins.push((b, 1));
            }
        }
        eprintln!("FFD atomic block packing (CPV blocks only, ignoring all other stmts):");
        eprintln!("  bins used: {}", bins.len());
        let cpv_floor = cpv_count.div_ceil(max_cpvs);
        eprintln!(
            "  CPV-cap floor (cpvs / cap): {} (current heuristic K = 13, MILP K = 12)",
            cpv_floor
        );

        // Verdict.
        let max_block = sorted.first().copied().unwrap_or(0);
        let threshold_block = max_stmts / max_cpvs; // 40/8 = 5
        let total_block_stmts: usize = sorted.iter().sum();
        let free_stmts = n.saturating_sub(total_block_stmts);
        eprintln!(
            "Block stmts: {}; free (non-block) stmts: ~{}",
            total_block_stmts, free_stmts,
        );
        eprintln!(
            "Largest block = {}; uniform-block threshold for atomic safety = {}",
            max_block, threshold_block,
        );
        if bins.len() <= cpv_floor {
            eprintln!(
                "  -> FFD on CPV blocks alone matches CPV floor (={}). Atomic block-based packing is",
                cpv_floor,
            );
            eprintln!(
                "     viable in principle for this fixture's actual block mix; the open question is"
            );
            eprintln!(
                "     whether the {} free statements + topo + other-resource caps fit within {} PODs.",
                free_stmts, bins.len(),
            );
            if max_block > threshold_block {
                eprintln!(
                    "  -> Caveat: largest block = {} > {} means a uniform workload at this block size"
                , max_block, threshold_block);
                eprintln!(
                    "     would regress. The mix (esp. {} small blocks at sizes 1-2) is what makes it work.",
                    hist.get(&1).copied().unwrap_or(0) + hist.get(&2).copied().unwrap_or(0),
                );
            }
        } else {
            eprintln!(
                "  -> FFD on CPV blocks alone needs {} bins > CPV floor {}: atomic block-based",
                bins.len(),
                cpv_floor,
            );
            eprintln!("     packing regresses.");
        }
    }

    /// Probe: does pre-emptively synth-ifying every external (input)
    /// statement on cracked-refinery drop K from 13 to 12? The fixture
    /// has 2 external pods x 1 input statement x 1 consumer each (so the
    /// existing 2+-consumer and feasibility republish rules don't fire).
    /// User's hypothesis is that proactively republishing into the chain
    /// lets the partition place the externals in PODs with spare capacity
    /// instead of forcing the consumer POD to open the external pod.
    #[test]
    fn cracked_refinery_preemptive_synth_probe() {
        use cost::StatementCost;
        let shape: InputShape =
            serde_json::from_str(CRACKED_REFINERY_FIXTURE).expect("fixture deserializes");
        let n_orig = shape.num_statements();
        let num_statements = shape.statement_pod.len();
        assert_eq!(
            num_statements, 2,
            "cracked-refinery has 2 external input statements"
        );

        // Build augmented dep_edges: replace each External with
        // Internal(n_orig + statement).
        let mut new_dep_edges: Vec<Vec<AbstractDep>> = shape
            .dep_edges
            .iter()
            .map(|edges| {
                edges
                    .iter()
                    .map(|dep| match dep {
                        AbstractDep::Internal(d) => AbstractDep::Internal(*d),
                        AbstractDep::External { statement, .. } => {
                            AbstractDep::Internal(n_orig + *statement)
                        }
                    })
                    .collect()
            })
            .collect();
        // Append synth statements with the External dep moved to them.
        for statement in 0..num_statements {
            new_dep_edges.push(vec![AbstractDep::External {
                pod: shape.statement_pod[statement],
                statement,
            }]);
        }
        let mut new_costs: Vec<StatementCost> = shape.costs.clone();
        for _ in 0..num_statements {
            new_costs.push(StatementCost::default());
        }
        let augmented = InputShape {
            costs: new_costs,
            dep_edges: new_dep_edges,
            output_public_indices: shape.output_public_indices.clone(),
            num_external_pods: shape.num_external_pods,
            statement_pod: shape.statement_pod.clone(),
            params: shape.params.clone(),
        };

        let baseline = partition::partition(&shape).expect("baseline partitions");
        let augmented_out = partition::partition(&augmented).expect("augmented partitions");
        eprintln!(
            "baseline K = {}, sizes = {:?}",
            baseline.pod_count,
            baseline
                .pod_statements
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>(),
        );
        eprintln!(
            "augmented (default prio) K = {}, sizes = {:?}",
            augmented_out.pod_count,
            augmented_out
                .pod_statements
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>(),
        );

        // Probe synth-first priority: give synths priority 0..S, originals
        // priority S..n. This forces bin-packing to place synths in the
        // earliest segment with capacity.
        let n_aug = augmented.num_statements();
        let mut prio: Vec<usize> = vec![0; n_aug];
        for (rank, p) in (n_orig..n_aug).enumerate() {
            prio[p] = rank;
        }
        for (rank, slot) in prio.iter_mut().take(n_orig).enumerate() {
            *slot = num_statements + rank;
        }
        let ord = partition::kahn_bin_packing(&augmented, &prio)
            .expect("synth-first bin-packing must produce an ordering");
        let synth_first_out = partition::partition_with_ordering(&augmented, &ord)
            .expect("DP must partition synth-first ordering");
        eprintln!(
            "augmented + synth-first prio bp K = {}, sizes = {:?}",
            synth_first_out.pod_count,
            synth_first_out
                .pod_statements
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>(),
        );

        // Per-POD CPV totals (synth-first augmented).
        let cpvs: Vec<usize> = synth_first_out
            .pod_statements
            .iter()
            .map(|stmts| {
                stmts
                    .iter()
                    .map(|&s| augmented.costs[s].custom_pred_verifications)
                    .sum()
            })
            .collect();
        eprintln!("  synth-first per-POD CPV: {:?}", cpvs);

        // Also try other generators with synth-first priority.
        if let Some(ord_prio) = partition::kahn_with_priority(&augmented, &prio) {
            if let Some(out) = partition::partition_with_ordering(&augmented, &ord_prio) {
                eprintln!("augmented + synth-first prio kahn K = {}", out.pod_count);
            }
        }
    }

    /// A non-statement-table cap (`max_signed_by`) forces a multi-POD
    /// split even though every POD has plenty of statement-table slack.
    /// Confirms the partitioner respects per-resource caps beyond
    /// `max_statements`.
    #[test]
    fn signed_by_limit_forces_multi_pod_split() {
        use crate::{
            backends::plonky2::{primitives::ec::schnorr::SecretKey, signer::Signer},
            frontend::SignedDictBuilder,
        };

        let params = Params {
            max_signed_by: 2,
            ..Params::default()
        };
        let vd_set = &*MOCK_VD_SET;
        let prover = MockProver {};

        let mut builder = MultiPodBuilder::new(&params, vd_set);
        for i in 0..4_i64 {
            let mut signed_builder = SignedDictBuilder::new(&params);
            signed_builder.insert("id", i);
            let signer = Signer(SecretKey((i as u32 + 1).into()));
            let signed_dict = signed_builder.sign(&signer).expect("sign dict");
            if i == 3 {
                builder
                    .pub_op(FrontendOp::dict_signed_by(&signed_dict))
                    .expect("pub signed_by");
            } else {
                builder
                    .priv_op(FrontendOp::dict_signed_by(&signed_dict))
                    .expect("priv signed_by");
            }
        }

        let solved = builder.solve().expect("should solve");
        assert_eq!(
            solved.solution().pod_count,
            2,
            "4 SignedBy ops with max_signed_by=2 require exactly 2 PODs"
        );
        let result = solved.prove(&prover).expect("prove should succeed");
        assert_eq!(result.pods.len(), 2);
        for (i, pod) in result.pods.iter().enumerate() {
            pod.pod
                .verify()
                .unwrap_or_else(|e| panic!("POD {} verification failed: {:?}", i, e));
        }
    }

    /// Hand-construct a `DependencyGraph` so we can exercise the pre-pass
    /// without rigging up a `MainPodBuilder` and prover.
    mod prepass_tests {
        use crate::{
            frontend::{
                multi_pod::{
                    build_shape_and_index,
                    deps::{DependencyGraph, ExternalDependency, StatementSource},
                    shape::AbstractDep,
                },
                Operation as FrontendOp,
            },
            middleware::{
                Hash, NativeOperation, OperationAux, OperationType, Params, RawValue, Statement,
                Value, ValueRef,
            },
        };

        fn noop_op() -> FrontendOp {
            FrontendOp(
                OperationType::Native(NativeOperation::None),
                vec![],
                OperationAux::None,
            )
        }

        fn ext_statement(pod_seed: i64, val: i64) -> ExternalDependency {
            // A unique pod hash per seed and a literal-Equal statement per
            // value. The statement contents are arbitrary as long as
            // different input statements hash differently.
            ExternalDependency {
                pod_hash: Hash::from(RawValue::from(pod_seed)),
                statement: Statement::Equal(
                    ValueRef::Literal(Value::from(val)),
                    ValueRef::Literal(Value::from(val)),
                ),
            }
        }

        #[test]
        fn single_consumer_does_not_republish() {
            let ext = ext_statement(1, 1);
            let deps = DependencyGraph {
                statement_deps: vec![vec![StatementSource::External(ext)]],
            };
            let operations = vec![noop_op()];
            let (shape, _index) =
                build_shape_and_index(&operations, &deps, &[], &Params::default());
            assert_eq!(shape.num_statements(), 1);
            assert!(matches!(
                shape.dep_edges[0][0],
                AbstractDep::External { .. }
            ));
        }

        #[test]
        fn two_consumers_trigger_republish() {
            let ext = ext_statement(1, 1);
            let deps = DependencyGraph {
                statement_deps: vec![
                    vec![StatementSource::External(ext.clone())],
                    vec![StatementSource::External(ext)],
                ],
            };
            let operations = vec![noop_op(), noop_op()];
            let (shape, _index) =
                build_shape_and_index(&operations, &deps, &[], &Params::default());

            assert_eq!(shape.num_statements(), 3);
            let synth_idx = 2;
            assert_eq!(shape.dep_edges[0], vec![AbstractDep::Internal(synth_idx)]);
            assert_eq!(shape.dep_edges[1], vec![AbstractDep::Internal(synth_idx)]);
            assert!(matches!(
                shape.dep_edges[synth_idx][0],
                AbstractDep::External { .. }
            ));
        }

        #[test]
        fn opportunistic_bundling_republishes_single_consumer_siblings() {
            // External pod 1 has input statement A (2 consumers) and input
            // statement B (1 consumer). A triggers the basic 2+-consumer
            // rule. Opportunistic bundling should pull B in too: the
            // synth-hosting POD pays for pod 1 once regardless, so
            // bundling B costs only one extra statement slot and frees
            // B's consumer from referencing pod 1 directly.
            let ext_a = ext_statement(1, 1);
            let ext_b = ext_statement(1, 2);
            let deps = DependencyGraph {
                statement_deps: vec![
                    vec![StatementSource::External(ext_a.clone())],
                    vec![StatementSource::External(ext_a)],
                    vec![StatementSource::External(ext_b.clone())],
                ],
            };
            let operations = vec![noop_op(), noop_op(), noop_op()];
            let (shape, _index) =
                build_shape_and_index(&operations, &deps, &[], &Params::default());

            // 3 originals + 2 synths (one per input statement of pod 1) = 5.
            assert_eq!(shape.num_statements(), 5);
            // Every original's external dep should be rewritten to Internal.
            for orig in 0..3 {
                assert!(
                    matches!(shape.dep_edges[orig][0], AbstractDep::Internal(_)),
                    "orig {} should reference a synth after bundling",
                    orig
                );
            }
        }

        #[test]
        fn bundling_does_not_cross_pods() {
            // Two separate external pods. Pod 1 has an input statement
            // with 2 consumers (triggers republish). Pod 2 has an input
            // statement with 1 consumer. Pod 2's input statement should
            // NOT be republished; bundling is per-pod.
            let p1 = ext_statement(1, 1);
            let p2 = ext_statement(2, 1);
            let deps = DependencyGraph {
                statement_deps: vec![
                    vec![StatementSource::External(p1.clone())],
                    vec![StatementSource::External(p1)],
                    vec![StatementSource::External(p2)],
                ],
            };
            let operations = vec![noop_op(), noop_op(), noop_op()];
            let (shape, _index) =
                build_shape_and_index(&operations, &deps, &[], &Params::default());

            // 3 originals + 1 synth (only pod 1's input statement) = 4.
            assert_eq!(shape.num_statements(), 4);
            // The pod-2 consumer keeps its External dep.
            assert!(matches!(
                shape.dep_edges[2][0],
                AbstractDep::External { .. }
            ));
        }

        #[test]
        fn distinct_statements_get_distinct_synthetics() {
            let ext_a = ext_statement(1, 1);
            let ext_b = ext_statement(1, 2);
            let deps = DependencyGraph {
                statement_deps: vec![
                    vec![StatementSource::External(ext_a.clone())],
                    vec![StatementSource::External(ext_a)],
                    vec![StatementSource::External(ext_b.clone())],
                    vec![StatementSource::External(ext_b)],
                ],
            };
            let operations = vec![noop_op(), noop_op(), noop_op(), noop_op()];
            let (shape, index) = build_shape_and_index(&operations, &deps, &[], &Params::default());

            assert_eq!(shape.num_statements(), 6);
            assert_eq!(index.statements.len(), 2);
            assert_eq!(shape.num_external_pods, 1);
        }
    }
}
