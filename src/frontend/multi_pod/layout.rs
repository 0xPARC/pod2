//! Reusable layouts for multi-POD packing.
//!
//! Solving the MILP is the expensive part of the multi-POD pipeline, but its
//! output depends only on the *structure* of the problem, not the concrete
//! values. So a layout computed once can be reused for any future invocation
//! with the same shape, e.g. a transaction type that always has the same
//! operation graph but different inputs.
//!
//! [`LayoutKey`] is `Serialize`, so it plugs into the existing `cache::get`
//! machinery (mem cache or disk cache, gated by features). See
//! [`crate::frontend::multi_pod::MultiPodBuilder::solve_cached`].

use std::collections::{BTreeSet, HashMap};

use serde::{Deserialize, Serialize};

use super::{
    cost::StatementCost,
    deps::{DependencyGraph, ExternalDependency, StatementSource},
    solver::MultiPodSolution,
    Result,
};
use crate::middleware::{Hash, Params, RawValue, Statement, Value, ValueRef};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AbstractDep {
    Internal(usize),
    External { pod: usize, premise: usize },
}

/// Structural shape of a multi-POD problem; the cache key for layouts.
///
/// Two builders with equal `LayoutKey`s always produce the same solver output,
/// regardless of concrete values, dict contents, or external pod hashes.
/// Marked `#[non_exhaustive]` so callers must obtain instances via
/// [`MultiPodBuilder::layout_key`] (or by deserializing) rather than struct
/// literals, which keeps the field invariants in this module's hands.
///
/// [`MultiPodBuilder::layout_key`]: super::MultiPodBuilder::layout_key
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct LayoutKey {
    pub costs: Vec<StatementCost>,
    pub dep_edges: Vec<Vec<AbstractDep>>,
    pub output_public_indices: Vec<usize>,
    pub params: Params,
    pub num_external_pods: usize,
    pub num_external_premises: usize,
}

/// The solver's assignment with positional (rather than concrete) external
/// references, so it can be reattached to any builder of the same shape.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct AbstractSolution {
    pub pod_count: usize,
    pub statement_to_pods: Vec<Vec<usize>>,
    pub pod_statements: Vec<Vec<usize>>,
    pub pod_public_statements: Vec<BTreeSet<usize>>,
    pub pod_internal_inputs: Vec<BTreeSet<usize>>,
    pub pod_external_inputs: Vec<BTreeSet<usize>>,
    pub pod_public_external_premises: Vec<BTreeSet<usize>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub struct Layout {
    pub key: LayoutKey,
    pub solution: AbstractSolution,
}

impl LayoutKey {
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

/// External pods and premises ordered by first appearance in the dependency
/// graph. The solver builds this same ordering internally, so positional
/// indices line up between cached layouts and live solver runs.
pub(super) struct CanonicalExternals<'a> {
    pub pods: Vec<Hash>,
    pub premises: Vec<ExternalDependency>,
    pub pod_idx: HashMap<Hash, usize>,
    pub premise_idx: HashMap<&'a ExternalDependency, usize>,
}

pub(super) fn canonicalize_externals(deps: &DependencyGraph) -> CanonicalExternals<'_> {
    let mut pods: Vec<Hash> = Vec::new();
    let mut pod_idx: HashMap<Hash, usize> = HashMap::new();
    let mut premises: Vec<ExternalDependency> = Vec::new();
    let mut premise_idx: HashMap<&ExternalDependency, usize> = HashMap::new();

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

/// Reconstruct a `DependencyGraph` from the abstract dep edges, using
/// synthetic external pod hashes and statements. The synthetic values are
/// deterministic functions of the positional indices so the solver's
/// canonical ordering will match the layout's.
pub(super) fn synthetic_deps_from_key(key: &LayoutKey) -> DependencyGraph {
    let pods: Vec<Hash> = (0..key.num_external_pods).map(synthetic_pod_hash).collect();
    let premises: Vec<Statement> = (0..key.num_external_premises)
        .map(synthetic_premise_statement)
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
                            pod_hash: pods[*pod],
                            statement: premises[*premise].clone(),
                        })
                    }
                })
                .collect()
        })
        .collect();

    DependencyGraph { statement_deps }
}

fn synthetic_pod_hash(pod_idx: usize) -> Hash {
    Hash::from(RawValue::from(pod_idx as i64))
}

fn synthetic_premise_statement(premise_idx: usize) -> Statement {
    let v = Value::from(premise_idx as i64);
    Statement::Equal(ValueRef::Literal(v.clone()), ValueRef::Literal(v))
}

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
