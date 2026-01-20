//! Dependency analysis for statements and operations.
//!
//! This module analyzes dependencies between statements to determine
//! which statements must be proved before others.

use std::collections::HashMap;

use crate::{
    frontend::{Operation, OperationArg},
    middleware::{Hash, Statement},
};

/// Represents a source of a statement dependency.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StatementSource {
    /// Statement created within this builder at the given index.
    Internal(usize),
    /// Statement from an external input POD (identified by POD hash).
    External(Hash),
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

                        deps.push(StatementSource::Internal(dep_idx));
                        continue;
                    }

                    // Check if this is from an external POD
                    if let Some(&pod_hash) = external_pod_statements.get(dep_stmt) {
                        deps.push(StatementSource::External(pod_hash));
                    } else {
                        // Statement arguments should either be internal (created earlier)
                        // or from external PODs. If neither, something is wrong.
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

    fn make_none_op() -> FrontendOp {
        FrontendOp(
            OperationType::Native(NativeOperation::None),
            vec![],
            OperationAux::None,
        )
    }

    fn make_copy_op(stmt: Statement) -> FrontendOp {
        FrontendOp(
            OperationType::Native(NativeOperation::CopyStatement),
            vec![OperationArg::Statement(stmt)],
            OperationAux::None,
        )
    }

    #[test]
    fn test_simple_dependency_graph() {
        // Test dependency chain: op0 creates s0, op1 references s0, op2 references op1's output.
        //
        // Each operation produces a distinct statement (as in the real system).
        // Dependencies are tracked by matching operation input statements to earlier outputs.
        //
        // Using meaningful values:
        // - s0 = Equal(100, 100) created by op0
        // - s1 = Equal(100, 100) is op1's output after copying s0 (same semantic value)
        // - s2 = Equal(100, 100) is op2's output after copying s1 (same semantic value)
        //
        // Note: Each statement object must be distinct for the HashMap to work correctly,
        // even if they represent the same logical value. In practice, the builder ensures this.
        let s0 = Statement::Equal(
            ValueRef::Literal(Value::from(100)),
            ValueRef::Literal(Value::from(100)),
        );
        let s1 = Statement::Equal(
            ValueRef::Literal(Value::from(101)), // Distinct from s0 for testing
            ValueRef::Literal(Value::from(101)),
        );
        let s2 = Statement::Equal(
            ValueRef::Literal(Value::from(102)), // Distinct from s1 for testing
            ValueRef::Literal(Value::from(102)),
        );

        let statements = vec![s0.clone(), s1.clone(), s2.clone()];
        let operations = vec![
            make_none_op(),           // op0: creates s0
            make_copy_op(s0.clone()), // op1: copies s0, depends on op0
            make_copy_op(s1.clone()), // op2: copies s1, depends on op1
        ];

        let graph = DependencyGraph::build(&statements, &operations, &HashMap::new());

        // Check dependencies
        assert!(
            graph.statement_deps[0].is_empty(),
            "op0 creates s0, no dependencies"
        );
        assert_eq!(
            graph.statement_deps[1].len(),
            1,
            "op1 copies s0, depends on op0"
        );
        assert_eq!(
            graph.statement_deps[2].len(),
            1,
            "op2 copies s1, depends on op1"
        );
    }
}
