use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

// Use publicly exported types from middleware
use crate::middleware::{self, OperationType, PodId, Statement, Value, Wildcard, F};

/// Type alias for mapping custom predicate references to their definitions.
// pub type CustomDefinitions = HashMap<CustomPredicateRef, CustomPredicate>;

/// Type alias for mapping canonical custom predicate identifiers (Vec<F>)
/// to their definitions. Based on prover.md Stage 1.
pub type CustomDefinitions = HashMap<Vec<F>, crate::middleware::CustomPredicate>;

pub type InitialFacts = Vec<(PodId, middleware::Statement)>;

/// The overall result of the translation stage.
pub struct TranslationOutput {
    pub custom_definitions: CustomDefinitions,
    pub initial_facts: InitialFacts,
}

// Represents a concrete value found during solving
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum ConcreteValue {
    Pod(PodId),
    Key(String), // Store Key name as String for simplicity
    Val(Value),
}

impl std::fmt::Display for ConcreteValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteValue::Pod(id) => write!(f, "Pod({})", id),
            ConcreteValue::Key(k) => write!(f, "Key({})", k),
            ConcreteValue::Val(v) => write!(f, "Val({})", v),
        }
    }
}

// Represents a single step in a proof deduction
#[derive(Debug, Clone, PartialEq, Eq, Hash)] // Eq requires wrapped types to implement Eq
pub struct ProofStep {
    /// The operation used in this step.
    pub operation: OperationType, // Use middleware::OperationType directly
    /// The statements used as input to the operation.
    pub inputs: Vec<Statement>, // Use middleware::Statement directly
    /// The statement derived by this step.
    pub output: Statement, // Use middleware::Statement directly
}

/// Represents a sequence of proof steps deriving a target statement.
/// Using a tuple struct for now based on previous linter errors.
#[derive(Clone, Debug, PartialEq, Eq, Hash)] // Assuming ProofChain needs these
pub struct ProofChain(pub Vec<ProofStep>);

/// Represents a successful proof outcome.
#[derive(Debug)]
pub struct ProofSolution {
    /// The final consistent assignment of wildcards to concrete values.
    pub bindings: HashMap<Wildcard, ConcreteValue>,
    /// The specific base statements (with their origin PodId) required for the proof.
    pub scope: HashSet<(PodId, Statement)>, // Use middleware::Statement
    /// The derived target statements mapped to their full proof chains.
    /// Keyed by the derived middleware::Statement.
    pub proof_chains: HashMap<Statement, ProofChain>, // Use middleware::Statement
}

// Remove incorrect re-exports - these types are defined in this module
// pub use crate::middleware::ProofSolution; // Re-export if needed
// pub use crate::middleware::ProofStep; // Re-export if needed
// pub use crate::middleware::ProofChain; // Re-export if needed
// pub use crate::middleware::ConcreteValue; // Re-export if needed
