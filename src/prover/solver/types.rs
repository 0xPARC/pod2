use std::collections::HashSet;

use crate::{
    middleware::{PodId, Value},
    prover::types::ConcreteValue,
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
