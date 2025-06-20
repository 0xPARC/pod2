use std::{collections::HashSet, fmt, sync::Arc};

use crate::{
    frontend::Operation,
    middleware::{
        AnchoredKey, CustomPredicateRef, NativeOperation, OperationAux, OperationType, Statement,
    },
};

/// The final output of a successful query. It represents the complete
/// and verifiable derivation path for the initial proof request.
#[derive(Clone, Debug)]
pub struct Proof {
    pub root_nodes: Vec<Arc<ProofNode>>,
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for node in &self.root_nodes {
            if !first {
                writeln!(f)?;
            }
            write!(f, "{}", node)?;
            first = false;
        }
        Ok(())
    }
}

/// A node in the proof tree. Each node represents a proven statement (the conclusion)
/// and the rule used to prove it (the justification).
#[derive(Clone, Debug)]
pub struct ProofNode {
    pub conclusion: Statement,
    pub justification: Justification,
}

impl ProofNode {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        let prefix = "  ".repeat(indent);
        writeln!(f, "{}{}", prefix, self.conclusion)?;

        let because_prefix = "  ".repeat(indent + 1);
        match &self.justification {
            Justification::Fact => {
                writeln!(f, "{}- by Fact", because_prefix)?;
            }
            Justification::ValueComparison(op) => {
                writeln!(f, "{}- by {:?}", because_prefix, *op)?;
            }
            Justification::Transitive(path) => {
                writeln!(f, "{}- by Transitivity via:", because_prefix)?;
                for key in path {
                    writeln!(f, "{}  - {}", because_prefix, key)?;
                }
            }
            Justification::Custom(cpr, premises) => {
                writeln!(f, "{}- by rule {}", because_prefix, cpr.predicate().name)?;
                for premise in premises {
                    premise.fmt_with_indent(f, indent + 2)?;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for ProofNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

/// Represents the logical rule used to justify a `ProofNode`'s conclusion.
#[derive(Clone, Debug)]
pub enum Justification {
    /// The conclusion is a known fact from the `FactDB`.
    Fact,
    /// The conclusion was derived by applying a native operation like `EqualFromEntries`.
    /// The premises are the child nodes in the proof tree.
    ValueComparison(NativeOperation),
    /// The conclusion was derived from a path in the equality graph.
    Transitive(Vec<AnchoredKey>),
    /// The conclusion was derived by applying a custom predicate.
    /// The premises for the custom predicate's body are the child nodes.
    Custom(CustomPredicateRef, Vec<Arc<ProofNode>>),
}

impl Proof {
    /// Performs a post-order traversal of the proof tree(s) and returns a
    /// flattened list of proof nodes. This ordering ensures that when iterating
    /// through the list, the premises of any given proof node have already
    /// been visited.
    pub fn walk_post_order(&self) -> Vec<Arc<ProofNode>> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();
        for node in &self.root_nodes {
            Self::post_order_traverse(node, &mut visited, &mut result);
        }
        result
    }

    /// Walks the proof graph in post-order and produces an `Operation` for each
    /// justification. The resulting vector of operations is ordered such that
    /// any operation's premises are guaranteed to have appeared earlier in the list.
    pub fn to_operations(&self) -> Vec<Operation> {
        self.walk_post_order()
            .into_iter()
            .map(|node| {
                match &node.justification {
                    Justification::Fact => {
                        // A fact from the DB is like an axiom.
                        // We can represent this operationally as copying the proven statement.
                        Operation(
                            OperationType::Native(NativeOperation::CopyStatement),
                            vec![node.conclusion.clone().into()],
                            OperationAux::None,
                        )
                    }
                    Justification::ValueComparison(op) => {
                        // A native comparison was performed.
                        // This is also like an axiom in the proof system.
                        Operation(
                            // TODO: Get the actual operation from the statement type??
                            OperationType::Native(*op),
                            vec![node.conclusion.clone().into()],
                            OperationAux::None,
                        )
                    }
                    Justification::Transitive(_path) => {
                        // To construct a `TransitiveEqualFromStatements` operation, we would need
                        // the two endpoint statements of the transitivity chain. The proof
                        // justification would need to be richer to support this.
                        // Stubbing for now.
                        Operation(
                            OperationType::Native(NativeOperation::None),
                            vec![],
                            OperationAux::None,
                        )
                    }
                    Justification::Custom(cpr, premises) => {
                        // The premises for a custom rule are the conclusions of the child proof nodes.
                        let premise_statements: Vec<Statement> =
                            premises.iter().map(|p| p.conclusion.clone()).collect();
                        Operation(
                            OperationType::Custom(cpr.clone()),
                            premise_statements.into_iter().map(|s| s.into()).collect(),
                            OperationAux::None,
                        )
                    }
                }
            })
            .collect()
    }

    fn post_order_traverse(
        node: &Arc<ProofNode>,
        visited: &mut HashSet<*const ProofNode>,
        result: &mut Vec<Arc<ProofNode>>,
    ) {
        let ptr = Arc::as_ptr(node);
        // We use a raw pointer comparison to handle proof DAGs correctly.
        if !visited.insert(ptr) {
            return; // Already visited
        }

        // Visit children first (post-order).
        // Only Custom justifications have premises in the tree structure.
        if let Justification::Custom(_, premises) = &node.justification {
            for premise in premises {
                Self::post_order_traverse(premise, visited, result);
            }
        }

        // Visit the node itself after its children.
        result.push(node.clone());
    }
}
