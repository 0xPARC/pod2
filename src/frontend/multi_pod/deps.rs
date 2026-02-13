//! Dependency analysis for statements and operations.
//!
//! This module analyzes dependencies between statements to determine
//! which statements must be proved before others.

use std::collections::HashMap;

use super::cost::AnchoredKeyId;
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
                        deps.push(StatementSource::External(pod_hash));
                    } else if AnchoredKeyId::from_contains_statement(dep_stmt).is_some() {
                        // Anchored-key Contains args may be implicit requirements that are
                        // auto-materialized by MainPodBuilder. They are handled by anchored-key
                        // resource accounting, not by statement dependency edges.
                        continue;
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
        dict,
        frontend::Operation as FrontendOp,
        middleware::{AnchoredKey, NativeOperation, OperationAux, OperationType, Value, ValueRef},
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

    /// CopyStatement(s) produces s (the same statement)
    fn copy_op(stmt: Statement) -> FrontendOp {
        FrontendOp(
            OperationType::Native(NativeOperation::CopyStatement),
            vec![OperationArg::Statement(stmt)],
            OperationAux::None,
        )
    }

    #[test]
    fn test_copy_creates_dependency_on_original() {
        // CopyStatement(s) produces s. When we copy a statement, the copy
        // depends on where that statement first appears.
        //
        // statements[0] = s (produced by none_op - not realistic, but we need a first occurrence)
        // statements[1] = s (produced by copy_op(s))
        //
        // op1's argument s matches statements[0], so statement 1 depends on statement 0.
        let s = equal_stmt(1);

        let statements = vec![s.clone(), s.clone()];
        let operations = vec![
            none_op(),  // Placeholder - in reality something else would produce s
            copy_op(s), // Copies s, producing s. Depends on statements[0].
        ];

        let graph = DependencyGraph::build(&statements, &operations, &HashMap::new());

        assert!(graph.statement_deps[0].is_empty());
        assert_eq!(graph.statement_deps[1], vec![StatementSource::Internal(0)]);
    }

    #[test]
    fn test_multiple_copies_depend_on_original() {
        // Multiple copies of the same statement all depend on where it first appears.
        let s = equal_stmt(1);

        let statements = vec![s.clone(), s.clone(), s.clone()];
        let operations = vec![none_op(), copy_op(s.clone()), copy_op(s)];

        let graph = DependencyGraph::build(&statements, &operations, &HashMap::new());

        assert!(graph.statement_deps[0].is_empty());
        assert_eq!(graph.statement_deps[1], vec![StatementSource::Internal(0)]);
        assert_eq!(graph.statement_deps[2], vec![StatementSource::Internal(0)]);
    }

    #[test]
    fn test_anchored_key_contains_arg_is_treated_as_implicit_requirement() {
        // A literal Contains statement can be used as an anchored-key argument even when
        // no explicit producer statement exists in internal/external statements, because
        // MainPodBuilder auto-inserts Contains statements for anchored keys.
        let dict = dict!({
            "k" => 7_i64
        });

        let anchored_contains = Statement::Contains(
            ValueRef::Literal(Value::from(dict.clone())),
            ValueRef::Literal(Value::from("k")),
            ValueRef::Literal(Value::from(7_i64)),
        );
        let ak = AnchoredKey::from((&dict, "k"));
        let produced_statement = Statement::Equal(ValueRef::Key(ak.clone()), ValueRef::Key(ak));

        // Use a typical frontend operation that consumes entry-like args.
        // We're only testing the dependency graph, not the actual proof, so the operation
        // just needs to have the right arguments to test what we're looking for.
        let statements = vec![produced_statement];
        let operations = vec![FrontendOp::eq(anchored_contains.clone(), anchored_contains)];

        let graph = DependencyGraph::build(&statements, &operations, &HashMap::new());

        assert!(graph.statement_deps[0].is_empty());
    }
}
