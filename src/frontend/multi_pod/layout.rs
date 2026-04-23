//! Reusable layouts for multi-POD packing.
//!
//! Solving the MILP is the expensive part of the multi-POD pipeline. For a fixed
//! set of operations and resource limits, the optimal layout (which statements go
//! in which POD, which are public, etc.) depends only on the *structure* of the
//! problem, not on the concrete values. So a layout computed once can be reused
//! for any future invocation that has the same structural shape.
//!
//! # Types
//!
//! - [`LayoutKey`]: the structural shape — operation costs, abstract dependency
//!   edges, public indices, params, and external pod count. Two problems with the
//!   same key always produce the same solver layout.
//! - [`Layout`]: the cached output — an [`AbstractSolution`] together with the key
//!   it was solved for.
//!
//! # Caching
//!
//! [`LayoutKey`] is `Serialize`/`Deserialize`, so it plugs directly into the
//! existing `cache::get` machinery (mem cache or disk cache, gated by features).
//! See [`crate::frontend::multi_pod::MultiPodBuilder::solve_cached`].

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::{
    cost::StatementCost,
    deps::{DependencyGraph, ExternalDependency, StatementSource},
    solver::MultiPodSolution,
    Result,
};
use crate::middleware::{Hash, Params, Statement, Value, ValueRef};

/// A dependency edge expressed without reference to concrete values.
///
/// Internal deps reference another statement by index. External deps reference
/// the source external pod and premise by their canonical (first-appearance)
/// position, not by hash or statement value.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AbstractDep {
    Internal(usize),
    External { pod: usize, premise: usize },
}

/// Structural shape of a multi-POD problem. Acts as the cache key for layouts.
///
/// Two builders with identical `LayoutKey`s will always produce the same solver
/// layout, regardless of the concrete `Statement` values, dict contents, or
/// external pod hashes involved.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LayoutKey {
    pub costs: Vec<StatementCost>,
    pub dep_edges: Vec<Vec<AbstractDep>>,
    pub output_public_indices: Vec<usize>,
    pub params: Params,
    pub num_external_pods: usize,
    pub num_external_premises: usize,
}

/// The solver's assignment, expressed without concrete external pod hashes.
///
/// Identical in structure to [`MultiPodSolution`] except that external references
/// are positional indices (matching the canonical ordering of external pods and
/// premises in the dependency graph).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractSolution {
    pub pod_count: usize,
    pub statement_to_pods: Vec<Vec<usize>>,
    pub pod_statements: Vec<Vec<usize>>,
    pub pod_public_statements: Vec<BTreeSet<usize>>,
    pub pod_internal_inputs: Vec<BTreeSet<usize>>,
    pub pod_external_inputs: Vec<BTreeSet<usize>>,
    pub pod_public_external_premises: Vec<BTreeSet<usize>>,
}

/// A reusable layout: the cache key paired with the solver's output.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Layout {
    pub key: LayoutKey,
    pub solution: AbstractSolution,
}

impl LayoutKey {
    /// Derive a key from the structural inputs of a solve.
    ///
    /// The canonical ordering of external pods and premises is by first
    /// appearance in `deps.statement_deps`, matching what the solver does
    /// internally.
    pub(super) fn from_inputs(
        costs: &[StatementCost],
        deps: &DependencyGraph,
        output_public_indices: &[usize],
        params: &Params,
    ) -> Self {
        let canonical = canonicalize_externals(deps);

        let dep_edges: Vec<Vec<AbstractDep>> = deps
            .statement_deps
            .iter()
            .map(|edges| {
                edges
                    .iter()
                    .map(|src| match src {
                        StatementSource::Internal(i) => AbstractDep::Internal(*i),
                        StatementSource::External(ext) => {
                            let pod = canonical.pod_idx[&ext.pod_hash];
                            let premise = canonical.premise_idx[ext];
                            AbstractDep::External { pod, premise }
                        }
                    })
                    .collect()
            })
            .collect();

        Self {
            costs: costs.to_vec(),
            dep_edges,
            output_public_indices: output_public_indices.to_vec(),
            params: params.clone(),
            num_external_pods: canonical.pods.len(),
            num_external_premises: canonical.premises.len(),
        }
    }
}

/// Canonical ordering of external pods and premises within a dependency graph.
///
/// Both are ordered by first appearance during left-to-right traversal of
/// `deps.statement_deps`. This matches the ordering the solver builds
/// internally, so positional indices line up across both worlds.
pub(super) struct CanonicalExternals<'a> {
    pub pods: Vec<Hash>,
    pub premises: Vec<ExternalDependency>,
    pub pod_idx: std::collections::HashMap<Hash, usize>,
    pub premise_idx: std::collections::HashMap<&'a ExternalDependency, usize>,
}

pub(super) fn canonicalize_externals(deps: &DependencyGraph) -> CanonicalExternals<'_> {
    let mut pods: Vec<Hash> = Vec::new();
    let mut pod_idx: std::collections::HashMap<Hash, usize> = std::collections::HashMap::new();
    let mut premises: Vec<ExternalDependency> = Vec::new();
    let mut premise_idx: std::collections::HashMap<&ExternalDependency, usize> =
        std::collections::HashMap::new();

    for edges in &deps.statement_deps {
        for src in edges {
            if let StatementSource::External(ext) = src {
                if let std::collections::hash_map::Entry::Vacant(e) = pod_idx.entry(ext.pod_hash) {
                    e.insert(pods.len());
                    pods.push(ext.pod_hash);
                }
                if !premise_idx.contains_key(ext) {
                    premise_idx.insert(ext, premises.len());
                    premises.push(ext.clone());
                }
            }
        }
    }

    CanonicalExternals {
        pods,
        premises,
        pod_idx,
        premise_idx,
    }
}

/// Project a concrete [`MultiPodSolution`] into the abstract form for caching.
pub(super) fn abstract_from_solution(solution: &MultiPodSolution) -> AbstractSolution {
    AbstractSolution {
        pod_count: solution.pod_count,
        statement_to_pods: solution.statement_to_pods.clone(),
        pod_statements: solution.pod_statements.clone(),
        pod_public_statements: solution.pod_public_statements.clone(),
        pod_internal_inputs: solution.pod_internal_inputs.clone(),
        pod_external_inputs: solution.pod_external_inputs.clone(),
        pod_public_external_premises: solution.pod_public_external_premises.clone(),
    }
}

/// Inflate an [`AbstractSolution`] into a [`MultiPodSolution`] using the
/// concrete external pod hashes and premises observed in the new builder.
pub(super) fn solution_from_abstract(
    abs: &AbstractSolution,
    external_pod_hashes: Vec<Hash>,
    external_premises: Vec<ExternalDependency>,
) -> MultiPodSolution {
    MultiPodSolution {
        pod_count: abs.pod_count,
        statement_to_pods: abs.statement_to_pods.clone(),
        pod_statements: abs.pod_statements.clone(),
        pod_public_statements: abs.pod_public_statements.clone(),
        pod_internal_inputs: abs.pod_internal_inputs.clone(),
        external_pod_hashes,
        pod_external_inputs: abs.pod_external_inputs.clone(),
        external_premises,
        pod_public_external_premises: abs.pod_public_external_premises.clone(),
    }
}

/// Reconstruct a [`DependencyGraph`] from a [`LayoutKey`], using synthetic
/// external pod hashes and statements.
///
/// The synthetic values are deterministic functions of the positional indices,
/// so they preserve the canonical ordering the solver expects. They never leak
/// outside the solver — only used for the MILP run that produces the layout.
pub(super) fn synth_deps_from_key(key: &LayoutKey) -> DependencyGraph {
    let synth_pods: Vec<Hash> = (0..key.num_external_pods).map(synth_pod_hash).collect();
    let synth_premises: Vec<Statement> = (0..key.num_external_premises)
        .map(synth_premise_statement)
        .collect();

    let statement_deps = key
        .dep_edges
        .iter()
        .map(|edges| {
            edges
                .iter()
                .map(|d| match d {
                    AbstractDep::Internal(i) => StatementSource::Internal(*i),
                    AbstractDep::External { pod, premise } => {
                        StatementSource::External(ExternalDependency {
                            pod_hash: synth_pods[*pod],
                            statement: synth_premises[*premise].clone(),
                        })
                    }
                })
                .collect()
        })
        .collect();

    DependencyGraph { statement_deps }
}

fn synth_pod_hash(pod_idx: usize) -> Hash {
    use crate::middleware::RawValue;
    Hash::from(RawValue::from(pod_idx as i64))
}

fn synth_premise_statement(premise_idx: usize) -> Statement {
    let v = Value::from(premise_idx as i64);
    Statement::Equal(ValueRef::Literal(v.clone()), ValueRef::Literal(v))
}

/// Validate that `actual` matches `expected`. Used by `apply_layout` to confirm
/// the cached layout is applicable to the new builder's shape.
pub(super) fn check_key_match(expected: &LayoutKey, actual: &LayoutKey) -> Result<()> {
    if expected == actual {
        Ok(())
    } else {
        Err(super::Error::Custom(format!(
            "layout shape mismatch: cached layout was solved for a different problem shape \
             (expected {} statements / {} ext pods / {} premises, got {} / {} / {})",
            expected.costs.len(),
            expected.num_external_pods,
            expected.num_external_premises,
            actual.costs.len(),
            actual.num_external_pods,
            actual.num_external_premises,
        )))
    }
}
