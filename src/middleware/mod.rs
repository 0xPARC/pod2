//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

mod basetypes;
pub mod containers;
mod custom;
mod operation;
mod statement;
pub use basetypes::*;
pub use custom::*;
pub use operation::*;
pub use statement::*;

use anyhow::Result;
use dyn_clone::DynClone;
use std::any::Any;
use std::collections::HashMap;
use std::fmt;

pub const SELF: PodId = PodId(SELF_ID_HASH);

impl fmt::Display for PodId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == SELF {
            write!(f, "self")
        } else if self.0 == EMPTY_HASH {
            write!(f, "null")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

/// AnchoredKey is a tuple containing (OriginId: PodId, key: Hash)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredKey(pub PodId, pub Hash);

impl AnchoredKey {
    pub fn origin(&self) -> PodId {
        self.0
    }
    pub fn key(&self) -> Hash {
        self.1
    }
}

impl fmt::Display for AnchoredKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.0, self.1)?;
        Ok(())
    }
}

/// An entry consists of a key-value pair.
pub type Entry = (String, Value);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct PodId(pub Hash);

impl ToFields for PodId {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        self.0.to_fields(params)
    }
}

pub enum PodType {
    None = 0,
    MockSigned = 1,
    MockMain = 2,
    Signed = 3,
    Main = 4,
}

impl From<PodType> for Value {
    fn from(v: PodType) -> Self {
        Value::from(v as i64)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
    pub max_operation_args: usize,
    // max number of statements that can be ANDed or ORed together
    // in a custom predicate
    pub max_custom_predicate_arity: usize,
    pub max_custom_batch_size: usize,
}

impl Default for Params {
    fn default() -> Self {
        Self {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 20,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 5,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
        }
    }
}

impl Params {
    pub fn max_priv_statements(&self) -> usize {
        self.max_statements - self.max_public_statements
    }

    pub fn statement_tmpl_arg_size() -> usize {
        2 * HASH_SIZE + 1
    }

    pub fn predicate_size() -> usize {
        HASH_SIZE + 2
    }

    pub fn statement_tmpl_size(&self) -> usize {
        Self::predicate_size() + self.max_statement_args * Self::statement_tmpl_arg_size()
    }

    pub fn custom_predicate_size(&self) -> usize {
        self.max_custom_predicate_arity * self.statement_tmpl_size() + 2
    }

    pub fn custom_predicate_batch_size_field_elts(&self) -> usize {
        self.max_custom_batch_size * self.custom_predicate_size()
    }

    pub fn print_serialized_sizes(&self) {
        println!("Parameter sizes:");
        println!(
            "  Statement template argument: {}",
            Self::statement_tmpl_arg_size()
        );
        println!("  Predicate: {}", Self::predicate_size());
        println!("  Statement template: {}", self.statement_tmpl_size());
        println!("  Custom predicate: {}", self.custom_predicate_size());
        println!(
            "  Custom predicate batch: {}",
            self.custom_predicate_batch_size_field_elts()
        );
        println!();
    }
}

pub trait Pod: fmt::Debug + DynClone {
    fn verify(&self) -> Result<()>;
    fn id(&self) -> PodId;
    fn pub_statements(&self) -> Vec<Statement>;
    /// Extract key-values from ValueOf public statements
    fn kvs(&self) -> HashMap<AnchoredKey, Value> {
        self.pub_statements()
            .into_iter()
            .filter_map(|st| match st {
                Statement::ValueOf(ak, v) => Some((ak, v)),
                _ => None,
            })
            .collect()
    }
    // Used for downcasting
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
}

// impl Clone for Box<dyn SignedPod>
dyn_clone::clone_trait_object!(Pod);

pub trait PodSigner {
    fn sign(&mut self, params: &Params, kvs: &HashMap<Hash, Value>) -> Result<Box<dyn Pod>>;
}

/// This is a filler type that fulfills the Pod trait and always verifies.  It's empty.  This
/// can be used to simulate padding in a circuit.
#[derive(Debug, Clone)]
pub struct NonePod {}

impl Pod for NonePod {
    fn verify(&self) -> Result<()> {
        Ok(())
    }
    fn id(&self) -> PodId {
        PodId(EMPTY_HASH)
    }
    fn pub_statements(&self) -> Vec<Statement> {
        Vec::new()
    }
    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct MainPodInputs<'a> {
    pub signed_pods: &'a [&'a Box<dyn Pod>],
    pub main_pods: &'a [&'a Box<dyn Pod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    /// Statements that need to be made public (they can come from input pods or input
    /// statements)
    pub public_statements: &'a [Statement],
}

pub trait PodProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>>;
}

pub trait ToFields {
    /// returns Vec<F> representation of the type
    fn to_fields(&self, params: &Params) -> Vec<F>;
}
