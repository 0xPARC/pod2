//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

use std::sync::Arc;
mod basetypes;
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    hash,
};

use anyhow::anyhow;
use containers::{Array, Dictionary, Set};
pub mod containers;
mod custom;
mod operation;
pub mod serialization;
mod statement;
use std::{any::Any, collections::HashMap, fmt};

use anyhow::Result;
pub use basetypes::*;
pub use custom::*;
use dyn_clone::DynClone;
pub use operation::*;
// use schemars::JsonSchema;
// use serde::{Deserialize, Serialize};
pub use statement::*;

pub const SELF: PodId = PodId(SELF_ID_HASH);

// TODO: Move all value-related types to to `value.rs`
#[derive(Clone, Debug)]
// TODO #[schemars(transform = serialization::transform_value_schema)]
pub enum TypedValue {
    // Serde cares about the order of the enum variants, with untagged variants
    // appearing at the end.
    // Variants without "untagged" will be serialized as "tagged" values by
    // default, meaning that a Set appears in JSON as {"Set":[...]}
    // and not as [...]
    // Arrays, Strings and Booleans are untagged, as there is a natural JSON
    // representation for them that is unambiguous to deserialize and is fully
    // compatible with the semantics of the POD types.
    // As JSON integers do not specify precision, and JavaScript is limited to
    // 53-bit precision for integers, integers are represented as tagged
    // strings, with a custom serializer and deserializer.
    // TAGGED TYPES:
    Set(Set),
    Dictionary(Dictionary),
    Int(
        // TODO #[serde(serialize_with = "serialize_i64", deserialize_with = "deserialize_i64")]
        // #[schemars(with = "String", regex(pattern = r"^\d+$"))]
        i64,
    ),
    // Uses the serialization for middleware::Value:
    Raw(RawValue),
    // UNTAGGED TYPES:
    // #[serde(untagged)]
    // #[schemars(skip)]
    Array(Array),
    // #[serde(untagged)]
    // #[schemars(skip)]
    String(String),
    // #[serde(untagged)]
    // #[schemars(skip)]
    Bool(bool),
}

impl From<&str> for TypedValue {
    fn from(s: &str) -> Self {
        TypedValue::String(s.to_string())
    }
}

impl From<String> for TypedValue {
    fn from(s: String) -> Self {
        TypedValue::String(s)
    }
}

impl From<i64> for TypedValue {
    fn from(v: i64) -> Self {
        TypedValue::Int(v)
    }
}

impl From<bool> for TypedValue {
    fn from(b: bool) -> Self {
        TypedValue::Bool(b)
    }
}

impl From<Hash> for TypedValue {
    fn from(h: Hash) -> Self {
        TypedValue::Raw(RawValue(h.0))
    }
}

impl From<Set> for TypedValue {
    fn from(s: Set) -> Self {
        TypedValue::Set(s)
    }
}

impl From<Dictionary> for TypedValue {
    fn from(d: Dictionary) -> Self {
        TypedValue::Dictionary(d)
    }
}

impl From<Array> for TypedValue {
    fn from(a: Array) -> Self {
        TypedValue::Array(a)
    }
}

impl From<RawValue> for TypedValue {
    fn from(v: RawValue) -> Self {
        TypedValue::Raw(v)
    }
}

impl From<PodType> for TypedValue {
    fn from(t: PodType) -> Self {
        TypedValue::from(t as i64)
    }
}

impl TryFrom<&TypedValue> for i64 {
    type Error = anyhow::Error;
    fn try_from(v: &TypedValue) -> std::result::Result<Self, Self::Error> {
        if let TypedValue::Int(n) = v {
            Ok(*n)
        } else {
            Err(anyhow!("Value not an int"))
        }
    }
}

impl fmt::Display for TypedValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypedValue::String(s) => write!(f, "\"{}\"", s),
            TypedValue::Int(v) => write!(f, "{}", v),
            TypedValue::Bool(b) => write!(f, "{}", b),
            TypedValue::Dictionary(d) => write!(f, "dict:{}", d.commitment()),
            TypedValue::Set(s) => write!(f, "set:{}", s.commitment()),
            TypedValue::Array(a) => write!(f, "arr:{}", a.commitment()),
            TypedValue::Raw(v) => write!(f, "{}", v),
        }
    }
}

impl From<&TypedValue> for RawValue {
    fn from(v: &TypedValue) -> Self {
        match v {
            TypedValue::String(s) => RawValue::from(hash_str(s)),
            TypedValue::Int(v) => RawValue::from(*v),
            TypedValue::Bool(b) => RawValue::from(*b as i64),
            TypedValue::Dictionary(d) => RawValue::from(d.commitment()),
            TypedValue::Set(s) => RawValue::from(s.commitment()),
            TypedValue::Array(a) => RawValue::from(a.commitment()),
            TypedValue::Raw(v) => *v,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Value {
    // The `TypedValue` is under `Arc` so that cloning a `Value` is cheap.
    typed: Arc<TypedValue>,
    raw: RawValue,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl Eq for Value {}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.raw.cmp(&other.raw))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl hash::Hash for Value {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.typed)
    }
}

impl Value {
    pub fn new(value: TypedValue) -> Self {
        let raw_value = RawValue::from(&value);
        Self {
            typed: Arc::new(value),
            raw: raw_value,
        }
    }

    pub fn typed(&self) -> &TypedValue {
        &self.typed
    }
    pub fn raw(&self) -> RawValue {
        self.raw
    }
}

// A Value can be created from any type Into<TypedValue> type: bool, string-like, i64, ...
impl<T> From<T> for Value
where
    T: Into<TypedValue>,
{
    fn from(t: T) -> Self {
        Self::new(t.into())
    }
}

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

impl From<&Value> for Hash {
    fn from(v: &Value) -> Self {
        Self(v.raw.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Key {
    name: String,
    hash: Hash,
}

impl Key {
    pub fn new(name: String) -> Self {
        let hash = hash_str(&name);
        Self { name, hash }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn hash(&self) -> Hash {
        self.hash
    }
    pub fn raw(&self) -> RawValue {
        RawValue(self.hash.0)
    }
}

// A Key can easily be created from a string-like type
impl<T> From<T> for Key
where
    T: Into<String>,
{
    fn from(t: T) -> Self {
        Self::new(t.into())
    }
}

impl ToFields for Key {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        self.hash.to_fields(params)
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

impl From<Key> for RawValue {
    fn from(key: Key) -> RawValue {
        RawValue(key.hash.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredKey {
    pub pod_id: PodId,
    pub key: Key,
}

impl AnchoredKey {
    pub fn new(pod_id: PodId, key: Key) -> Self {
        Self { pod_id, key }
    }
}

impl fmt::Display for AnchoredKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.pod_id, self.key)?;
        Ok(())
    }
}

impl<T> From<(PodId, T)> for AnchoredKey
where
    T: Into<Key>,
{
    fn from((pod_id, t): (PodId, T)) -> Self {
        Self::new(pod_id, t.into())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct PodId(pub Hash);

impl ToFields for PodId {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        self.0.to_fields(params)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PodType {
    None = 0,
    MockSigned = 1,
    MockMain = 2,
    Signed = 3,
    Main = 4,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::None => write!(f, "None"),
            PodType::MockSigned => write!(f, "MockSigned"),
            PodType::MockMain => write!(f, "MockMain"),
            PodType::Signed => write!(f, "Signed"),
            PodType::Main => write!(f, "Main"),
        }
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
    pub max_custom_predicate_wildcards: usize,
    pub max_custom_batch_size: usize,
    // maximum number of merkle proofs
    pub max_merkle_proofs: usize,
    // maximum depth for merkle tree gadget
    pub max_depth_mt_gadget: usize,
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
            max_custom_predicate_wildcards: 10,
            max_custom_batch_size: 5,
            max_merkle_proofs: 5,
            max_depth_mt_gadget: 32,
        }
    }
}

impl Params {
    pub fn max_priv_statements(&self) -> usize {
        self.max_statements - self.max_public_statements
    }

    pub const fn statement_tmpl_arg_size() -> usize {
        2 * HASH_SIZE + 1
    }

    pub const fn predicate_size() -> usize {
        HASH_SIZE + 2
    }

    pub const fn operation_type_size() -> usize {
        HASH_SIZE + 2
    }

    pub fn statement_size(&self) -> usize {
        Self::predicate_size() + STATEMENT_ARG_F_LEN * self.max_statement_args
    }

    pub fn operation_size(&self) -> usize {
        Self::operation_type_size() + OPERATION_ARG_F_LEN * self.max_operation_args
    }

    pub const fn statement_tmpl_size(&self) -> usize {
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
    fn as_any(&self) -> &dyn Any;
    // Front-end Pods keep references to middleware Pods. Most of the
    // middleware data can be derived directly from front-end data, but the
    // "proof" data is only created at the point of proving/signing, and
    // cannot be reconstructed. As such, we need to serialize it whenever
    // we serialize a front-end Pod. Since the front-end does not understand
    // the implementation details of the middleware, this method allows the
    // middleware to provide some serialized data that can be used to
    // reconstruct the proof.
    fn serialized_proof(&self) -> String;
}

// impl Clone for Box<dyn SignedPod>
dyn_clone::clone_trait_object!(Pod);

pub trait PodSigner {
    fn sign(&mut self, params: &Params, kvs: &HashMap<Key, Value>) -> Result<Box<dyn Pod>>;
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
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn serialized_proof(&self) -> String {
        "".to_string()
    }
}

#[derive(Debug)]
pub struct MainPodInputs<'a> {
    pub signed_pods: &'a [&'a dyn Pod],
    pub main_pods: &'a [&'a dyn Pod],
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
