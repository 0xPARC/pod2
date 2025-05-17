use std::collections::{HashMap, HashSet};

use crate::{
    middleware::{
        PodId, Predicate, Statement, StatementArg, ToFields, Value, Wildcard, WildcardValue, F,
    },
    prover::{
        error::ProverError,
        types::{ConcreteValue, ProofChain},
    },
};

// Represents the set of possible concrete values for a wildcard
pub type Domain = HashSet<ConcreteValue>;

// Represents structural constraints derived directly from StatementTmpls
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
    // e.g., ?A must be a PodId
    Type {
        wildcard: super::Wildcard, // Use super::Wildcard
        expected_type: ExpectedType,
    },
    // e.g., ?A["foo"] constraint on ?A
    LiteralKey {
        pod_wildcard: super::Wildcard, // Use super::Wildcard
        literal_key: String,
    },
    // e.g., PodX[?Y] constraint on ?Y
    LiteralOrigin {
        key_wildcard: super::Wildcard, // Use super::Wildcard
        literal_pod_id: PodId,
    },
    // e.g., ?A[?Y] constraint relating ?Y to ?A
    WildcardOrigin {
        key_wildcard: super::Wildcard,
        pod_wildcard: super::Wildcard,
    },
    // e.g., ValueOf(..., ?V) where ?V must match a literal value arg
    LiteralValue {
        wildcard: super::Wildcard, // Use super::Wildcard
        literal_value: Value,
    },
}

// Placeholder for the expected type of a wildcard during initialization
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub enum ExpectedType {
    Pod,
    Key,
    Val,
    Unknown, // Initial state before type is inferred
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum MemoizationKey {
    Native(Statement),
    Custom {
        predicate_ref_id: Vec<F>, // Canonical ID for the CustomPredicateRef
        args: Vec<WildcardValue>, // Concrete arguments to the custom predicate
    },
}

#[derive(Debug, Clone)]
pub enum MemoizedProofOutcome {
    Success(ProofChain, HashSet<(PodId, Statement)>), // Proof chain and its specific scope fragment
    Failure(ProverError),
}
