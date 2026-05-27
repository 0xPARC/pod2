//! Dependency analysis for statements and operations.

use std::collections::HashMap;

use crate::{
    frontend::{Operation, OperationArg},
    middleware::{
        Hash, InputPodOpenStatement, NativeOperation, OperationAux, OperationType, Statement,
    },
};

/// Reference to a statement sourced from an external input POD.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExternalDependency {
    /// Hash of the external POD containing `statement` in its public set.
    pub pod_hash: Hash,
    /// The statement value itself.
    pub statement: Statement,
}

/// Concrete source of a statement dependency. The canonicalisation step
/// converts this to a positional `AbstractDep`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StatementSource {
    /// Statement created within this builder at the given index.
    Internal(usize),
    /// Statement from an external input POD.
    External(ExternalDependency),
}

/// Dependency graph for all statements in a builder. `statement_deps[i]` is
/// the list of dependencies of statement `i`, in argument order.
#[derive(Clone, Debug)]
pub struct DependencyGraph {
    pub statement_deps: Vec<Vec<StatementSource>>,
}

impl DependencyGraph {
    /// Build the dependency graph from parallel `statements` and
    /// `operations` arrays (where `operations[i]` produces `statements[i]`)
    /// plus a `statement -> pod hash` map for recognising external
    /// references.
    pub fn build(
        statements: &[Statement],
        operations: &[Operation],
        external_pod_statements: &HashMap<Statement, Hash>,
    ) -> Self {
        let mut statement_deps = Vec::with_capacity(statements.len());

        // Map statement content to its first-occurrence index. First-wins
        // so that if the same content appears more than once, later ops
        // referencing it point at the earliest producer rather than at
        // themselves.
        let mut statement_to_index: HashMap<&Statement, usize> = HashMap::new();
        for (i, s) in statements.iter().enumerate() {
            if !s.is_none() {
                statement_to_index.entry(s).or_insert(i);
            }
        }

        for (idx, op) in operations.iter().enumerate() {
            let mut deps = Vec::new();

            for arg in &op.1 {
                if let OperationArg::Statement(ref dep_stmt) = arg {
                    if dep_stmt.is_none() {
                        continue;
                    }

                    if let Some(&dep_idx) = statement_to_index.get(dep_stmt) {
                        assert!(
                            dep_idx <= idx,
                            "Statement at index {} depends on future statement at index {}",
                            idx,
                            dep_idx
                        );

                        if dep_idx < idx {
                            deps.push(StatementSource::Internal(dep_idx));
                            continue;
                        }
                        // dep_idx == idx: the first occurrence of this
                        // statement content is at the current position,
                        // meaning this operation both takes and produces
                        // it. Fall through to the external lookup below.
                    }

                    if let Some(&pod_hash) = external_pod_statements.get(dep_stmt) {
                        deps.push(StatementSource::External(ExternalDependency {
                            pod_hash,
                            statement: dep_stmt.clone(),
                        }));
                    } else {
                        unreachable!(
                            "Statement argument not found in internal statements or external PODs: {:?}",
                            dep_stmt
                        );
                    }
                }
            }

            // `OpenInputStatement` carries no arg statements; its dependency
            // on the source pod is implicit in the aux's `sts_root`.
            // Materialize it as an External dep here so the partitioner
            // accounts for the input-tree slot and the external-pod reference.
            if let OperationType::Native(NativeOperation::OpenInputStatement) = op.0 {
                if let OperationAux::OpenInputStatement(InputPodOpenStatement {
                    sts_root, ..
                }) = &op.2
                {
                    deps.push(StatementSource::External(ExternalDependency {
                        pod_hash: *sts_root,
                        statement: statements[idx].clone(),
                    }));
                }
            }

            statement_deps.push(deps);
        }

        Self { statement_deps }
    }
}
