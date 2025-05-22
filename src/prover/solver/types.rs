use std::collections::{HashMap, HashSet};

use crate::{
    middleware::{
        Key, Params, PodId, Statement, StatementTmpl, TypedValue, Value, Wildcard, WildcardValue, F,
    },
    prover::{
        error::ProverError,
        indexing::ProverIndexes,
        types::{ConcreteValue, CustomDefinitions, ProofChain},
    },
};

// Represents the set of possible concrete values for a wildcard
pub type Domain = HashSet<ConcreteValue>;

// Represents structural constraints derived directly from StatementTmpls
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint {
    // e.g., ?A must be a PodId
    Type {
        wildcard: Wildcard,
        expected_type: ExpectedType,
    },
    // e.g., ?A["foo"] constraint on ?A
    LiteralKey {
        pod_wildcard: Wildcard,
        literal_key: String,
    },
    // e.g., PodX[?Y] constraint on ?Y
    LiteralOrigin {
        key_wildcard: Wildcard,
        literal_pod_id: PodId,
    },
    // e.g., ?A[?Y] constraint relating ?Y to ?A
    WildcardOrigin {
        key_wildcard: Wildcard,
        pod_wildcard: Wildcard,
    },
    // e.g., ValueOf(..., ?V) where ?V must match a literal value arg
    LiteralValue {
        wildcard: Wildcard,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WildcardInterpretation {
    PublicArg(usize),       // Index of the public argument
    PrivateLocal(Wildcard), // The actual private wildcard
    Global(Wildcard),       // The actual global wildcard from top-level request
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

pub struct GlobalContext<'env> {
    pub indexes: &'env ProverIndexes,
    pub custom_definitions: &'env CustomDefinitions,
    pub params: &'env Params,
    pub potential_constant_info: &'env [(Wildcard, Key, Value)],
}

pub struct ResolveScope<'scope> {
    pub templates_to_resolve: &'scope [StatementTmpl],
    pub constraints: Vec<Constraint>,
    pub search_targets: Option<HashSet<Wildcard>>,
    pub wildcard_interpretation_map: HashMap<Wildcard, WildcardInterpretation>,
    pub public_arg_bindings: Option<&'scope HashMap<usize, WildcardValue>>,
    pub current_depth: usize,
    pub parent_custom_call_key: Option<MemoizationKey>,
}

/// Extension trait for `ConcreteValue` to convert to `WildcardValue`
pub trait ToWildcardValue {
    fn to_wildcard_value(&self) -> Result<WildcardValue, ProverError>;
}

impl ToWildcardValue for ConcreteValue {
    fn to_wildcard_value(&self) -> Result<WildcardValue, ProverError> {
        match self {
            ConcreteValue::Pod(id) => Ok(WildcardValue::PodId(*id)),
            ConcreteValue::Key(k_name) => Ok(WildcardValue::Key(Key::new(k_name.clone()))),
            ConcreteValue::Val(v_val) => Err(ProverError::Internal(format!(
                "Cannot convert ConcreteValue::Val ({:?}) directly to WildcardValue for memoization key argument.",
                v_val
            ))),
        }
    }
}

impl ToWildcardValue for crate::middleware::Value {
    fn to_wildcard_value(&self) -> Result<WildcardValue, ProverError> {
        match self.typed() {
            TypedValue::String(s) => Ok(WildcardValue::Key(Key::new(s.clone()))),
            // For memoization keys, we generally only expect PodId or Key as arguments to custom predicates.
            // If other Value types are needed, this conversion needs to be more robust or the MemoKey::Custom args need to change.
            _ => Err(ProverError::Internal(format!(
                "Cannot convert Literal Value ({:?}) directly to WildcardValue for memoization key argument. Expected String for Key.",
                self.typed()
            ))),
        }
    }
}
