//! Shared types for multi-POD solver solutions.
//!
//! Contains the solution representation (`MultiPodSolution`) and solver input
//! (`SolverInput`).

use std::collections::BTreeSet;

use crate::{
    frontend::multi_pod::{
        cost::StatementCost,
        deps::{DependencyGraph, ExternalDependency},
    },
    middleware::{Hash, Params},
};

/// Solution to the multi-POD packing problem.
///
/// Describes how statements are assigned to pods, which statements are
/// public in each pod, and how pods are wired together via internal and
/// external inputs.
#[derive(Debug)]
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

/// Input to the solver.
#[derive(Debug)]
pub struct SolverInput<'a> {
    /// Resource costs for each statement (one per statement, so `costs.len()`
    /// is the total number of statements).
    pub costs: &'a [StatementCost],

    /// Dependency graph.
    pub deps: &'a DependencyGraph,

    /// Indices of statements that must be public in output PODs.
    pub output_public_indices: &'a [usize],

    /// Parameters defining per-POD limits.
    pub params: &'a Params,

    /// Maximum number of PODs the solver will consider.
    pub max_pods: usize,
}
