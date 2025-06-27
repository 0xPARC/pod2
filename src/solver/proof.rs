use std::{
    collections::{HashMap, HashSet},
    fmt,
    sync::Arc,
};

use crate::{
    frontend::{Operation, OperationArg},
    middleware::{
        CustomPredicateRef, NativeOperation, OperationAux, OperationType, PodId, Predicate,
        Statement, StatementArg, ValueRef,
    },
    solver::{db::FactDB, semantics::predicates::PredicateHandler},
};

/// The final output of a successful query. It represents the complete
/// and verifiable derivation path for the initial proof request.
#[derive(Clone, Debug)]
pub struct Proof {
    pub root_nodes: Vec<Arc<ProofNode>>,
    pub db: Arc<FactDB>,
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
    pub statement: Statement,
    pub justification: Justification,
}

impl ProofNode {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        let prefix = "  ".repeat(indent);
        writeln!(f, "{}{}", prefix, self.statement)?;

        let because_prefix = "  ".repeat(indent + 1);
        match &self.justification {
            Justification::Fact => {
                writeln!(f, "{}- by Fact", because_prefix)?;
            }
            Justification::ValueComparison(op) => {
                writeln!(f, "{}- by {:?}", because_prefix, *op)?;
            }
            Justification::Custom(cpr, premises) => {
                writeln!(f, "{}- by rule {}", because_prefix, cpr.predicate().name)?;
                for premise in premises {
                    premise.fmt_with_indent(f, indent + 2)?;
                }
            }
            Justification::Special(op) => {
                writeln!(f, "{}- by {:?}", because_prefix, *op)?;
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
    /// The conclusion was derived by applying a custom predicate.
    /// The premises for the custom predicate's body are the child nodes.
    Custom(CustomPredicateRef, Vec<Arc<ProofNode>>),
    Special(NativeOperation),
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
    pub fn to_operations(&self) -> Vec<(Operation, bool)> {
        // Identify nodes that correspond to the *direct premises* of the synthetic
        // `_request_goal` root.  Those should become **public** operations.

        let mut public_nodes: std::collections::HashSet<*const ProofNode> =
            std::collections::HashSet::new();

        for root in &self.root_nodes {
            if let Justification::Custom(_, premises) = &root.justification {
                for p in premises {
                    public_nodes.insert(Arc::as_ptr(p));
                }
            }
        }

        self.walk_post_order()
            .into_iter()
            .flat_map(|node| {
                let is_public = public_nodes.contains(&Arc::as_ptr(&node));

                let ops: Vec<Operation> = match &node.justification {
                    Justification::Fact => {
                        vec![Operation(
                            OperationType::Native(NativeOperation::CopyStatement),
                            vec![node.statement.clone().into()],
                            OperationAux::None,
                        )]
                    }
                    Justification::Special(_op) => {
                        if let Predicate::Native(pred) = node.statement.predicate() {
                            let handler = PredicateHandler::for_native_predicate(pred);
                            let args: Vec<ValueRef> = node
                                .statement
                                .args()
                                .iter()
                                .map(|a| a.try_into().unwrap())
                                .collect();
                            handler.explain_special_derivation(&args, &self.db).unwrap()
                        } else {
                            panic!("Special justification for non-native predicate");
                        }
                    }
                    Justification::ValueComparison(op) => {
                        let op_args: Vec<OperationArg> = node
                            .statement
                            .args()
                            .iter()
                            .map(|a| match a {
                                StatementArg::Key(k) => {
                                    self.db.anchored_key_to_equal_statement(k).unwrap().into()
                                }
                                StatementArg::Literal(l) => OperationArg::Literal(l.clone()),
                                _ => panic!("Invalid statement arg"),
                            })
                            .collect();

                        vec![Operation(
                            OperationType::Native(*op),
                            op_args,
                            OperationAux::None,
                        )]
                    }
                    Justification::Custom(cpr, premises) => {
                        // Skip the synthetic helper predicate added by the planner.
                        if cpr.predicate().name == "_request_goal" {
                            Vec::new()
                        } else {
                            let premise_statements: Vec<Statement> =
                                premises.iter().map(|p| p.statement.clone()).collect();
                            vec![Operation(
                                OperationType::Custom(cpr.clone()),
                                premise_statements.into_iter().map(|s| s.into()).collect(),
                                OperationAux::None,
                            )]
                        }
                    }
                };

                ops.into_iter()
                    .map(|op| (op, is_public))
                    .collect::<Vec<_>>()
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

    /// Returns the minimal set of PODs that provide every EDB statement referenced
    /// by the proof together with the list of operations (same as `to_operations`).
    pub fn to_inputs(&self) -> (Vec<PodId>, Vec<(Operation, bool)>) {
        let ops_with_flag = self.to_operations();

        // Collect every Statement that is passed as an OperationArg *and* exists in the EDB.
        // Map statement → set of providers
        let mut stmt_providers: HashMap<Statement, HashSet<PodId>> = HashMap::new();

        for (op, _public) in &ops_with_flag {
            for arg in &op.1 {
                if let OperationArg::Statement(st) = arg {
                    if let Some(provs) = providers_for_statement(&self.db, st) {
                        stmt_providers.entry(st.clone()).or_default().extend(provs);
                    }
                }
            }
        }

        // Greedy set cover ----------------------------------------------------
        let mut uncovered: HashSet<Statement> = stmt_providers.keys().cloned().collect();
        let mut pod_cover: Vec<PodId> = Vec::new();

        // Pre-select pods for statements with a single provider.
        for (st, pods) in &stmt_providers {
            if pods.len() == 1 {
                let p = *pods.iter().next().unwrap();
                if !pod_cover.contains(&p) {
                    pod_cover.push(p);
                }
            }
        }

        // Mark statements already covered by the pre-selection
        uncovered.retain(|st| {
            let providers = &stmt_providers[st];
            !providers.iter().any(|p| pod_cover.contains(p))
        });

        while !uncovered.is_empty() {
            // find pod with max uncovered coverage
            let (best_pod, _count) = stmt_providers
                .values()
                .flatten()
                .filter(|p| !pod_cover.contains(p))
                .map(|p| {
                    let c = uncovered
                        .iter()
                        .filter(|st| stmt_providers[*st].contains(p))
                        .count();
                    (p, c)
                })
                .max_by_key(|(_, c)| *c)
                .expect("No provider found for uncovered statements");

            pod_cover.push(*best_pod);

            uncovered.retain(|st| !stmt_providers[st].contains(best_pod));
        }

        (pod_cover, ops_with_flag)
    }
}

/// Returns the set of PodIds that assert the given statement, if any.
fn providers_for_statement(
    db: &FactDB,
    st: &Statement,
) -> Option<std::collections::HashSet<PodId>> {
    use std::collections::HashSet;

    use crate::middleware::{Predicate, ValueRef};

    match st {
        Statement::Equal(a, b) => db
            .get_binary_statement_index(&crate::middleware::NativePredicate::Equal)
            .and_then(|idx| idx.get(&[a.clone(), b.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::NotEqual(a, b) => db
            .get_binary_statement_index(&crate::middleware::NativePredicate::NotEqual)
            .and_then(|idx| idx.get(&[a.clone(), b.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::Lt(a, b) => db
            .get_binary_statement_index(&crate::middleware::NativePredicate::Lt)
            .and_then(|idx| idx.get(&[a.clone(), b.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::LtEq(a, b) => db
            .get_binary_statement_index(&crate::middleware::NativePredicate::LtEq)
            .and_then(|idx| idx.get(&[a.clone(), b.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::Contains(r, k, v) => db
            .get_ternary_statement_index(&crate::middleware::NativePredicate::Contains)
            .and_then(|idx| idx.get(&[r.clone(), k.clone(), v.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::NotContains(r, k) => db
            .get_binary_statement_index(&crate::middleware::NativePredicate::NotContains)
            .and_then(|idx| idx.get(&[r.clone(), k.clone()]).cloned())
            .map(HashSet::from_iter),
        Statement::Custom(cpr, vals) => {
            let key = (cpr.batch.id(), cpr.index, vals.clone());
            db.statement_index
                .custom
                .get(&key)
                .cloned()
                .map(HashSet::from_iter)
        }
        // Other native predicates can be added here as needed.
        _ => None,
    }
}
