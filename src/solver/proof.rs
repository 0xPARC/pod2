use std::sync::Arc;

use crate::middleware::{AnchoredKey, CustomPredicateRef, Statement};

/// The final output of a successful query. It represents the complete
/// and verifiable derivation path for the initial proof request.
#[derive(Clone, Debug)]
pub struct Proof {
    pub root_nodes: Vec<Arc<ProofNode>>,
}

/// A node in the proof tree. Each node represents a proven statement (the conclusion)
/// and the rule used to prove it (the justification).
#[derive(Clone, Debug)]
pub struct ProofNode {
    pub conclusion: Statement,
    pub justification: Justification,
}

/// Represents the logical rule used to justify a `ProofNode`'s conclusion.
#[derive(Clone, Debug)]
pub enum Justification {
    /// The conclusion is a known fact from the `FactDB`.
    Fact,
    /// The conclusion was derived by applying a native operation like `EqualFromEntries`.
    /// The premises are the child nodes in the proof tree.
    ValueComparison,
    /// The conclusion was derived from a path in the equality graph.
    Transitive(Vec<AnchoredKey>),
    /// The conclusion was derived by applying a custom predicate.
    /// The premises for the custom predicate's body are the child nodes.
    Custom(CustomPredicateRef, Vec<Arc<ProofNode>>),
}
