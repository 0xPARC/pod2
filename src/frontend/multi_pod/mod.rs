//! Multi-POD builder for the Merkle statement tree design.
//!
//! The solver is purely symbolic: it consumes a positional [`InputShape`]
//! and produces a positional [`OutputShape`]. The build layer in this
//! module translates between user-facing builder state and the symbolic
//! representation, holding an internal side table that maps positional
//! indices back to concrete pod hashes and external (input) statements.
//!
//! `solve()` partitions the workload symbolically; `prove()` then walks
//! the partition and builds + proves each POD in chain order.

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

use cost::OperationCost;
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
            max_open_input_statement_ops: usize::MAX / 2,
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
        let costs: Vec<OperationCost> = self
            .builder
            .operations
            .iter()
            .map(|op| OperationCost::from_operation(op, &self.params))
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
        let chain_capacity = 2usize.pow(BASE_PARAMS.max_depth_public_statements_mt as u32);
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
            builder.extend_input_pod0_public_statements()?;
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
                    // Output-public produced upstream; open from chain.
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
        let detail = diagnostics::diagnose_failure(shape)
            .map(|v| format!(": {}", v))
            .unwrap_or_default();
        Error::NoFeasiblePartition(format!(
            "the {} could not find a feasible partition under the current \
             params{}",
            kind, detail
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
    // frees downstream consumers from re-referencing E.
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
    let mut costs: Vec<OperationCost> = operations
        .iter()
        .map(|op| OperationCost::from_operation(op, params))
        .collect();
    costs.extend((0..n_synth).map(|_| OperationCost::default()));

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
    /// reaches K=13. MILP+cap reaches K=12, so the gap is 1 POD.
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
            max_signed_by_ops: 2,
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
