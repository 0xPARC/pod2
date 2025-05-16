//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

use std::sync::Arc;
mod basetypes;
use std::{
    cmp::{Ordering, PartialEq, PartialOrd},
    hash,
};

use containers::{Array, Dictionary, Set};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
pub mod containers;
mod custom;
mod error;
mod operation;
pub mod serialization;
mod statement;
use std::{any::Any, collections::HashMap, fmt};

pub use basetypes::*;
pub use custom::*;
use dyn_clone::DynClone;
pub use error::*;
pub use operation::*;
use serialization::*;
pub use statement::*;

use crate::backends::plonky2::primitives::merkletree::MerkleProof;

pub const SELF: PodId = PodId(SELF_ID_HASH);

// TODO: Move all value-related types to to `value.rs`
#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
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
        #[serde(serialize_with = "serialize_i64", deserialize_with = "deserialize_i64")]
        // #[schemars(with = "String", regex(pattern = r"^\d+$"))]
        i64,
    ),
    // Uses the serialization for middleware::Value:
    Raw(RawValue),
    // UNTAGGED TYPES:
    #[serde(untagged)]
    Array(Array),
    #[serde(untagged)]
    String(String),
    #[serde(untagged)]
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
    type Error = Error;
    fn try_from(v: &TypedValue) -> std::result::Result<Self, Self::Error> {
        if let TypedValue::Int(n) = v {
            Ok(*n)
        } else {
            Err(Error::custom("Value not an int".to_string()))
        }
    }
}

impl TryFrom<TypedValue> for Key {
    type Error = Error;
    fn try_from(tv: TypedValue) -> Result<Self> {
        match tv {
            TypedValue::String(s) => Ok(Key::new(s)),
            _ => Err(Error::custom(format!(
                "Value {} cannot be converted to a key.",
                tv
            ))),
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

// Schemars/JsonSchema can't handle Serde's "untagged" variants.
// Instead, we have to implement schema generation directly. It's not as
// complicated as it looks, though.
// We have to generate schemas for each of the variants, and then combine them
// into a single schema using the `anyOf` keyword.
// If we add a new variant, we will have to update this function.
impl JsonSchema for TypedValue {
    fn schema_name() -> String {
        "TypedValue".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        use schemars::schema::{InstanceType, Schema, SchemaObject, SingleOrVec};

        let set_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                properties: [("Set".to_string(), gen.subschema_for::<Set>())]
                    .into_iter()
                    .collect(),
                required: ["Set".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        let dictionary_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                properties: [("Dictionary".to_string(), gen.subschema_for::<Dictionary>())]
                    .into_iter()
                    .collect(),
                required: ["Dictionary".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        // Int is serialized/deserialized as a tagged string
        let int_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                properties: [(
                    "Int".to_string(),
                    Schema::Object(SchemaObject {
                        instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::String))),
                        metadata: Some(Box::new(schemars::schema::Metadata {
                            description: Some("An i64 represented as a string.".to_string()),
                            ..Default::default()
                        })),
                        ..Default::default()
                    }),
                )]
                .into_iter()
                .collect(),
                required: ["Int".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        let raw_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                properties: [("Raw".to_string(), gen.subschema_for::<RawValue>())]
                    .into_iter()
                    .collect(),
                required: ["Raw".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        // This is the part that Schemars can't generate automatically:
        let untagged_array_schema = gen.subschema_for::<Array>();
        let untagged_string_schema = gen.subschema_for::<String>();
        let untagged_bool_schema = gen.subschema_for::<bool>();

        Schema::Object(SchemaObject {
            subschemas: Some(Box::new(schemars::schema::SubschemaValidation {
                any_of: Some(vec![
                    Schema::Object(set_schema),
                    Schema::Object(dictionary_schema),
                    Schema::Object(int_schema),
                    Schema::Object(raw_schema),
                    untagged_array_schema,
                    untagged_string_schema,
                    untagged_bool_schema,
                ]),
                ..Default::default()
            })),
            metadata: Some(Box::new(schemars::schema::Metadata {
                description: Some("Represents various POD value types. Array, String, and Bool variants are represented untagged in JSON.".to_string()),
                ..Default::default()
            })),
            ..Default::default()
        })
    }
}

#[derive(Clone, Debug)]
pub struct Value {
    // The `TypedValue` is under `Arc` so that cloning a `Value` is cheap.
    typed: Arc<TypedValue>,
    raw: RawValue,
}

// Values are serialized as their TypedValue.
impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.typed.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let typed = TypedValue::deserialize(deserializer)?;
        Ok(Value::new(typed))
    }
}

impl JsonSchema for Value {
    fn schema_name() -> String {
        "Value".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        // Just use the schema of TypedValue since that's what we're actually serializing
        <TypedValue>::json_schema(gen)
    }
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
    /// Determines Merkle existence proof for `key` in `self` (if applicable).
    pub(crate) fn prove_existence<'a>(
        &'a self,
        key: &'a Value,
    ) -> Result<(&'a Value, MerkleProof)> {
        match &self.typed() {
            TypedValue::Array(a) => match key.typed() {
                TypedValue::Int(i) if i >= &0 => a.prove((*i) as usize),
                _ => Err(Error::custom(format!(
                    "Invalid key {} for container {}.",
                    key, self
                )))?,
            },
            TypedValue::Dictionary(d) => d.prove(&key.typed().clone().try_into()?),
            TypedValue::Set(s) => Ok((key, s.prove(key)?)),
            _ => Err(Error::custom(format!(
                "Invalid container value {}",
                self.typed()
            ))),
        }
    }
    /// Determines Merkle non-existence proof for `key` in `self` (if applicable).
    pub(crate) fn prove_nonexistence<'a>(&'a self, key: &'a Value) -> Result<MerkleProof> {
        match &self.typed() {
            TypedValue::Array(_) => Err(Error::custom(
                "Arrays do not support `NotContains` operation.".to_string(),
            )),
            TypedValue::Dictionary(d) => d.prove_nonexistence(&key.typed().clone().try_into()?),
            TypedValue::Set(s) => s.prove_nonexistence(key),
            _ => Err(Error::custom(format!(
                "Invalid container value {}",
                self.typed()
            ))),
        }
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

// When serializing a Key, we serialize only the name field, and not the hash.
// We can't directly tell Serde to render the whole struct as a string, so we
// implement our own serialization. It's important that if we change the
// structure of the Key struct, we update this implementation.
impl Serialize for Key {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.name.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Key {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let name = String::deserialize(deserializer)?;
        Ok(Key::new(name))
    }
}

// As per the above, we implement custom serialization for the Key type, and
// Schemars can't automatically generate a schema for it. Instead, we tell it
// to use the standard String schema.
impl JsonSchema for Key {
    fn schema_name() -> String {
        "Key".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        <String>::json_schema(gen)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize, JsonSchema)]
pub struct PodId(pub Hash);

impl ToFields for PodId {
    fn to_fields(&self, params: &Params) -> Vec<F> {
        self.0.to_fields(params)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
    pub max_operation_args: usize,
    // max number of custom predicates batches that a MainPod can use
    pub max_custom_predicate_batches: usize,
    // max number of operations using custom predicates that can be verified in the MainPod
    pub max_custom_predicate_verifications: usize,
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
            max_custom_predicate_batches: 2,
            max_custom_predicate_verifications: 5,
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

pub type DynError = dyn std::error::Error + Send + Sync;

pub trait Pod: fmt::Debug + DynClone + Any {
    fn verify(&self) -> Result<(), Box<DynError>>;
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

    // Front-end Pods keep references to middleware Pods. Most of the
    // middleware data can be derived directly from front-end data, but the
    // "proof" data is only created at the point of proving/signing, and
    // cannot be reconstructed. As such, we need to serialize it whenever
    // we serialize a front-end Pod. Since the front-end does not understand
    // the implementation details of the middleware, this method allows the
    // middleware to provide some serialized data that can be used to
    // reconstruct the proof.
    // It is an important principle that this data is opaque to the front-end
    // and any third-party code.
    fn serialized_proof(&self) -> String;
}

// impl Clone for Box<dyn SignedPod>
dyn_clone::clone_trait_object!(Pod);

pub trait PodSigner {
    fn sign(
        &mut self,
        params: &Params,
        kvs: &HashMap<Key, Value>,
    ) -> Result<Box<dyn Pod>, Box<DynError>>;
}

/// This is a filler type that fulfills the Pod trait and always verifies.  It's empty.  This
/// can be used to simulate padding in a circuit.
#[derive(Debug, Clone)]
pub struct NonePod {}

impl Pod for NonePod {
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(())
    }
    fn id(&self) -> PodId {
        PodId(EMPTY_HASH)
    }
    fn pub_statements(&self) -> Vec<Statement> {
        Vec::new()
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
    fn prove(
        &mut self,
        params: &Params,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn Pod>, Box<DynError>>;
}

pub trait ToFields {
    /// returns Vec<F> representation of the type
    fn to_fields(&self, params: &Params) -> Vec<F>;
}
