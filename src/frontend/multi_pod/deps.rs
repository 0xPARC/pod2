//! Dependency analysis for statements and operations.
//!
//! This module analyzes dependencies between statements to determine
//! which statements must be proved before others.

use std::collections::HashMap;

use crate::{
    frontend::{Operation, OperationArg},
    middleware::{Hash, Statement},
};

/// Reference to a statement sourced from an external input POD.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExternalDependency {
    /// Hash of the external POD containing `statement` in its public set.
    pub pod_hash: Hash,
    /// The statement value itself.
    pub statement: Statement,
}

/// Represents a source of a statement dependency.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StatementSource {
    /// Statement created within this builder at the given index.
    Internal(usize),
    /// Statement from an external input POD.
    External(ExternalDependency),
}

/// Dependency graph for all statements in a builder.
///
/// Each element `statement_deps[i]` is the list of dependencies for statement `i`.
#[derive(Clone, Debug)]
pub struct DependencyGraph {
    /// Dependencies for each statement (indexed by statement index).
    pub statement_deps: Vec<Vec<StatementSource>>,
}

impl DependencyGraph {
    /// Build a dependency graph from statements and operations.
    ///
    /// `statements` and `operations` should be parallel arrays where
    /// `operations[i]` produces `statements[i]`.
    ///
    /// `external_pod_statements` maps (pod_hash, statement) pairs to enable
    /// recognizing references to external POD statements.
    pub fn build(
        statements: &[Statement],
        operations: &[Operation],
        external_pod_statements: &HashMap<Statement, Hash>,
    ) -> Self {
        let mut statement_deps = Vec::with_capacity(statements.len());

        // Build a map from statement to its index for internal lookup.
        // Use entry().or_insert() to preserve the FIRST occurrence of each statement.
        // This is important for CopyStatement: if statements[0] = A and statements[2] = copy(A) = A,
        // we want statement_to_index[A] = 0 (the original), not 2 (the copy).
        let mut statement_to_index: HashMap<&Statement, usize> = HashMap::new();
        for (i, s) in statements.iter().enumerate() {
            if !s.is_none() {
                statement_to_index.entry(s).or_insert(i);
            }
        }

        for (idx, op) in operations.iter().enumerate() {
            let mut deps = Vec::new();

            // Examine each argument to the operation
            for arg in &op.1 {
                if let OperationArg::Statement(ref dep_stmt) = arg {
                    if dep_stmt.is_none() {
                        continue;
                    }

                    // Check if this is an internal statement (created earlier in this builder)
                    if let Some(&dep_idx) = statement_to_index.get(dep_stmt) {
                        // Internal dependencies must always be from earlier statements
                        assert!(
                            dep_idx <= idx,
                            "Statement at index {} depends on future statement at index {}",
                            idx,
                            dep_idx
                        );

                        if dep_idx < idx {
                            // The statement was created by an earlier operation
                            deps.push(StatementSource::Internal(dep_idx));
                            continue;
                        }
                        // dep_idx == idx: The first occurrence of this statement is at the current index,
                        // meaning this operation both takes and produces this statement (e.g., CopyStatement
                        // copying from an external POD). Fall through to check external PODs for the source.
                    }

                    // Check if this is from an external POD
                    if let Some(&pod_hash) = external_pod_statements.get(dep_stmt) {
                        deps.push(StatementSource::External(ExternalDependency {
                            pod_hash,
                            statement: dep_stmt.clone(),
                        }));
                    } else {
                        // Statement arguments should either be internal (created earlier)
                        // or from external PODs (except anchored-key implicit Contains).
                        // If neither, something is wrong.
                        unreachable!(
                            "Statement argument not found in internal statements or external PODs: {:?}",
                            dep_stmt
                        );
                    }
                }
            }

            statement_deps.push(deps);
        }

        Self { statement_deps }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        frontend::Operation as FrontendOp,
        middleware::{NativeOperation, OperationAux, OperationType, Value, ValueRef},
    };

    fn equal_stmt(n: i64) -> Statement {
        Statement::Equal(
            ValueRef::Literal(Value::from(n)),
            ValueRef::Literal(Value::from(n)),
        )
    }

    /// None operation produces Statement::None
    fn none_op() -> FrontendOp {
        FrontendOp(
            OperationType::Native(NativeOperation::None),
            vec![],
            OperationAux::None,
        )
    }
}
