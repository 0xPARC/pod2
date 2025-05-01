use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

// Use publicly exported types from the middleware module.
use crate::middleware::{self, OperationType, PodId, Statement, Value, Wildcard, F};

/// Type alias for mapping custom predicate references to their definitions.
/// The key is the canonical representation (Vec<F>) derived from the predicate.
/// Based on prover.md Stage 1.
pub type CustomDefinitions = HashMap<Vec<F>, crate::middleware::CustomPredicate>;

/// Represents the initial facts provided to the prover, typically derived from input PODs.
/// Each fact is a `Statement` associated with the `PodId` of its origin.
pub type InitialFacts = Vec<(PodId, middleware::Statement)>;

/// The overall result of the translation stage, containing processed custom definitions
/// and the collated initial facts.
pub struct TranslationOutput {
    pub custom_definitions: CustomDefinitions,
    pub initial_facts: InitialFacts,
}

/// Represents a concrete value binding discovered during the solving process.
/// This could be a PodId, a Key name, or a literal Value.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum ConcreteValue {
    Pod(PodId),
    Key(String), // Key name as String
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

/// Represents a single deduction step within a proof chain.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofStep {
    /// The operation (native or custom) performed in this step.
    pub operation: OperationType,
    /// The input statements required by the operation.
    pub inputs: Vec<Statement>,
    /// The output statement derived by this step.
    pub output: Statement,
}

/// Represents a sequence of `ProofStep`s demonstrating how a target statement was derived.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProofChain(pub Vec<ProofStep>);

/// Represents a successful proof outcome from the solver.
pub struct ProofSolution {
    /// The final, consistent assignment of wildcards to concrete values.
    pub bindings: HashMap<Wildcard, ConcreteValue>,
    /// The minimal set of base statements (from input PODs, with their origin `PodId`)
    /// required to justify the derived target statements.
    pub scope: HashSet<(PodId, Statement)>,
    /// The derived target statements mapped to their full proof chains.
    /// Keyed by the derived `Statement`.
    pub proof_chains: HashMap<Statement, ProofChain>,
}

// Remove incorrect re-exports - these types are defined in this module
// pub use crate::middleware::ProofSolution; // Re-export if needed
// pub use crate::middleware::ProofStep; // Re-export if needed
// pub use crate::middleware::ProofChain; // Re-export if needed
// pub use crate::middleware::ConcreteValue; // Re-export if needed
