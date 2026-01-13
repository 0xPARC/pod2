//! Dependency analysis for statements and operations.
//!
//! This module analyzes dependencies between statements to determine
//! which statements must be proved before others.

use std::collections::{HashMap, VecDeque};

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

/// Dependency information for a single statement.
#[derive(Clone, Debug)]
pub struct StatementDeps {
    /// The index of this statement in the builder.
    pub index: usize,
    /// Dependencies on other statements.
    pub depends_on: Vec<StatementSource>,
}

/// Dependency graph for all statements in a builder.
#[derive(Clone, Debug)]
pub struct DependencyGraph {
    /// Dependencies for each statement (indexed by statement index).
    pub statement_deps: Vec<StatementDeps>,
    /// Reverse mapping: which statements depend on a given internal statement.
    pub dependents: HashMap<usize, Vec<usize>>,
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
        let mut dependents: HashMap<usize, Vec<usize>> = HashMap::new();

        // Build a map from statement to its index for internal lookup
        let statement_to_index: HashMap<&Statement, usize> = statements
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.is_none())
            .map(|(i, s)| (s, i))
            .collect();

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
                            dependents.entry(dep_idx).or_default().push(idx);
                            continue;
                        }
                        // dep_idx == idx: This operation produces this statement (e.g., CopyStatement
                        // where output == input). Fall through to check external PODs for the source.
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

            statement_deps.push(StatementDeps {
                index: idx,
                depends_on: deps,
            });
        }

        Self {
            statement_deps,
            dependents,
        }
    }

    /// Compute a topological ordering of statements.
    ///
    /// Returns indices in an order where dependencies come before dependents.
    /// This uses Kahn's algorithm.
    pub fn topological_order(&self) -> Vec<usize> {
        let n = self.statement_deps.len();
        if n == 0 {
            return vec![];
        }

        // Count incoming edges (internal dependencies) for each node
        let mut in_degree = vec![0usize; n];
        for deps in &self.statement_deps {
            for dep in &deps.depends_on {
                if matches!(dep, StatementSource::Internal(_)) {
                    in_degree[deps.index] += 1;
                }
            }
        }

        // Start with nodes that have no dependencies (use FIFO to preserve original order)
        let mut queue: VecDeque<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
        let mut result = Vec::with_capacity(n);

        while let Some(node) = queue.pop_front() {
            result.push(node);

            // Decrease in_degree for all dependents
            if let Some(deps) = self.dependents.get(&node) {
                for &dependent in deps {
                    in_degree[dependent] -= 1;
                    if in_degree[dependent] == 0 {
                        queue.push_back(dependent);
                    }
                }
            }
        }

        // If result doesn't contain all nodes, there's a cycle (shouldn't happen)
        assert_eq!(result.len(), n, "Dependency graph has a cycle!");

        result
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
            graph.statement_deps[0].depends_on.is_empty(),
            "op0 creates s0, no dependencies"
        );
        assert_eq!(
            graph.statement_deps[1].depends_on.len(),
            1,
            "op1 copies s0, depends on op0"
        );
        assert_eq!(
            graph.statement_deps[2].depends_on.len(),
            1,
            "op2 copies s1, depends on op1"
        );

        // Check topological order
        let order = graph.topological_order();
        assert_eq!(order.len(), 3);

        // op0 -> op1 -> op2 (dependency chain)
        let pos_op0 = order.iter().position(|&x| x == 0).unwrap();
        let pos_op1 = order.iter().position(|&x| x == 1).unwrap();
        let pos_op2 = order.iter().position(|&x| x == 2).unwrap();
        assert!(pos_op0 < pos_op1, "op0 must come before op1");
        assert!(pos_op1 < pos_op2, "op1 must come before op2");
    }
}
