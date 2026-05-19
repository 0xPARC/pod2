//! Symbolic problem definition for the multi-POD-tree solver.
//!
//! [`InputShape`] captures the structure of a packing problem in positional
//! form, with no concrete POD hashes or statement values. The build layer
//! in `mod.rs` holds a side table that maps the indices back to concrete
//! data after solving. [`OutputShape`] is the solver's positional answer.
//!
//! Two builders that produce equal `InputShape`s (after canonicalisation)
//! produce equal `OutputShape`s, so this type doubles as a cache key if a
//! plan cache is later layered on top.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::cost::StatementCost;
use crate::middleware::Params;

/// A positional dependency. Internal points at another statement in the
/// same problem; External points at a `(pod, input-statement)` pair indexed
/// into the side-table held by the build layer.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AbstractDep {
    /// Reference to another statement at the given index in this problem.
    Internal(usize),
    /// Reference to an external POD's published statement.
    External {
        /// Index into the side table's external-pod list.
        pod: usize,
        /// Index into the side table's external-statement list.
        statement: usize,
    },
}

/// Symbolic input to the solver: the structure of a multi-POD problem in
/// positional form.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct InputShape {
    /// Per-statement resource costs.
    pub costs: Vec<StatementCost>,
    /// For each statement, the list of dependencies (in original order).
    pub dep_edges: Vec<Vec<AbstractDep>>,
    /// Statements that must be visible in the output POD's fresh tree.
    pub output_public_indices: Vec<usize>,
    /// Number of distinct external input PODs referenced by `dep_edges`.
    pub num_external_pods: usize,
    /// For each external (input) statement, the external-pod index it
    /// lives in.
    pub statement_pod: Vec<usize>,
    /// Per-POD resource limits.
    pub params: Params,
}

impl InputShape {
    /// Number of statements in the problem.
    pub fn num_statements(&self) -> usize {
        self.costs.len()
    }

    /// Number of distinct external input statements referenced by
    /// `dep_edges`.
    pub fn num_external_statements(&self) -> usize {
        self.statement_pod.len()
    }

    /// Per-statement internal-consumer index. `consumers()[d]` lists the
    /// statements that name `d` via `AbstractDep::Internal`. Order
    /// reflects the user's `dep_edges` order; entries may repeat if a
    /// statement names the same producer twice (callers needing dedup
    /// should handle that on the boundary).
    pub fn consumers(&self) -> Vec<Vec<usize>> {
        let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); self.num_statements()];
        for (s, deps) in self.dep_edges.iter().enumerate() {
            for dep in deps {
                if let AbstractDep::Internal(d) = dep {
                    consumers[*d].push(s);
                }
            }
        }
        consumers
    }

    /// Per-statement (`indegree`, `consumers`) pair built in one pass.
    /// `indegree[s]` counts internal dependencies of `s`; `consumers` is
    /// as in [`Self::consumers`]. Shared Kahn preamble.
    pub fn indegree_and_consumers(&self) -> (Vec<usize>, Vec<Vec<usize>>) {
        let n = self.num_statements();
        let mut indegree = vec![0_usize; n];
        let mut consumers: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (s, deps) in self.dep_edges.iter().enumerate() {
            for dep in deps {
                if let AbstractDep::Internal(d) = dep {
                    consumers[*d].push(s);
                    indegree[s] += 1;
                }
            }
        }
        (indegree, consumers)
    }
}

/// Symbolic output of the solver: a positional partition of statements
/// into a chain of PODs.
///
/// Only the load-bearing decisions are stored; everything else (which
/// statements get appended to the chain tree, which input pods each POD
/// references, etc.) is derivable from `pod_statements`,
/// `pod_republished_externals`, and the [`InputShape`] the partition was
/// computed from. See the helper methods for derivations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct OutputShape {
    /// Number of PODs in the chain. The last POD (`pod_count - 1`) is the
    /// output POD and publishes a fresh tree of `output_public_indices`.
    pub pod_count: usize,
    /// For each POD, the statements produced there. Indices are into the
    /// `InputShape`'s statement list. Within each POD the list is in
    /// ascending index order.
    pub pod_statements: Vec<Vec<usize>>,
    /// For each POD, external (input) statements that this POD imports
    /// from an
    /// external input and appends to the chain tree so that downstream
    /// PODs can reach them via slot 0 instead of re-referencing the
    /// source external POD.
    pub pod_republished_externals: Vec<BTreeSet<usize>>,
}

impl OutputShape {
    /// True if `pod_idx` is the output POD.
    pub fn is_output_pod(&self, pod_idx: usize) -> bool {
        pod_idx + 1 == self.pod_count
    }

    /// Returns the POD index in which statement `stmt` is produced, or
    /// `None` if the statement isn't placed (shouldn't happen for a valid
    /// partition; the assertion in `validate` covers this).
    pub fn pod_of(&self, stmt: usize) -> Option<usize> {
        for (pod_idx, stmts) in self.pod_statements.iter().enumerate() {
            if stmts.binary_search(&stmt).is_ok() {
                return Some(pod_idx);
            }
        }
        None
    }
}
