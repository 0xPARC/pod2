//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

use std::sync::Arc;

use hex::ToHex;
use itertools::Itertools;
use strum_macros::FromRepr;

mod basetypes;
use std::{cmp::PartialEq, hash};

use containers::{Array, Dictionary, Set};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
pub mod containers;
mod custom;
mod error;
mod operation;
mod pod_deserialization;
pub mod serialization;
mod statement;
use std::{any::Any, fmt};

pub use basetypes::*;
pub use custom::*;
use dyn_clone::DynClone;
pub use error::*;
pub use operation::*;
pub use pod_deserialization::*;
use serialization::*;
pub use statement::*;

use crate::backends::plonky2::primitives::merkletree::{
    MerkleProof, MerkleTreeStateTransitionProof,
};

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
    Int(
        #[serde(serialize_with = "serialize_i64", deserialize_with = "deserialize_i64")]
        // #[schemars(with = "String", regex(pattern = r"^\d+$"))]
        i64,
    ),
    // Uses the serialization for middleware::Value:
    Raw(RawValue),
    // Schnorr public key variant (EC point)
    PublicKey(PublicKey),
    // Schnorr secret key variant (scalar)
    SecretKey(SecretKey),
    // UNTAGGED TYPES:
    #[serde(untagged)]
    Set(Set),
    #[serde(untagged)]
    Dictionary(Dictionary),
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

impl From<PublicKey> for TypedValue {
    fn from(p: PublicKey) -> Self {
        TypedValue::PublicKey(p)
    }
}

impl From<SecretKey> for TypedValue {
    fn from(sk: SecretKey) -> Self {
        TypedValue::SecretKey(sk)
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

impl TryFrom<&TypedValue> for String {
    type Error = Error;
    fn try_from(tv: &TypedValue) -> Result<Self> {
        match tv {
            TypedValue::String(s) => Ok(s.clone()),
            _ => Err(Error::custom(format!(
                "Value {} cannot be converted to a string.",
                tv
            ))),
        }
    }
}

impl TryFrom<&TypedValue> for Key {
    type Error = Error;
    fn try_from(tv: &TypedValue) -> Result<Self> {
        Ok(Key::new(String::try_from(tv)?))
    }
}

impl TryFrom<&TypedValue> for PublicKey {
    type Error = Error;
    fn try_from(v: &TypedValue) -> std::result::Result<Self, Self::Error> {
        if let TypedValue::PublicKey(pk) = v {
            Ok(*pk)
        } else {
            Err(Error::custom("Value not a public key".to_string()))
        }
    }
}

impl TryFrom<&TypedValue> for SecretKey {
    type Error = Error;
    fn try_from(v: &TypedValue) -> std::result::Result<Self, Self::Error> {
        if let TypedValue::SecretKey(sk) = v {
            Ok(sk.clone())
        } else {
            Err(Error::custom("Value not a secret key".to_string()))
        }
    }
}

impl fmt::Display for TypedValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypedValue::Int(i) => write!(f, "{}", i),
            TypedValue::String(s) => {
                // Use serde_json for proper JSON-style escaping
                match serde_json::to_string(s) {
                    Ok(escaped) => write!(f, "{}", escaped),
                    Err(_) => write!(f, "\"{}\"", s),
                }
            }
            TypedValue::Bool(b) => write!(f, "{}", b),
            TypedValue::Array(a) => {
                write!(f, "[")?;
                for (i, v) in a.array().iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            TypedValue::Dictionary(d) => {
                write!(f, "{{ ")?;
                let kvs: Vec<_> = d.kvs().iter().sorted_by_key(|(k, _)| k.name()).collect();
                for (i, (k, v)) in kvs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, " }}")
            }
            TypedValue::Set(s) => {
                write!(f, "#[")?;
                let values: Vec<_> = s.set().iter().sorted_by_key(|k| k.raw()).collect();
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            TypedValue::PublicKey(p) => write!(f, "PublicKey({})", p),
            TypedValue::SecretKey(p) => write!(f, "SecretKey({})", p),
            TypedValue::Raw(r) => {
                write!(f, "Raw(0x{})", r.encode_hex::<String>())
            }
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
            TypedValue::PublicKey(p) => RawValue::from(hash_fields(&p.as_fields())),
            TypedValue::SecretKey(sk) => RawValue::from(hash_fields(&sk.to_limbs())),
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

        let root_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                properties: [("Root".to_string(), gen.subschema_for::<Hash>())]
                    .into_iter()
                    .collect(),
                required: ["Root".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        let public_key_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                // PublicKey is serialized as a string
                properties: [("PublicKey".to_string(), gen.subschema_for::<String>())]
                    .into_iter()
                    .collect(),
                required: ["PublicKey".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        let secret_key_schema = schemars::schema::SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(schemars::schema::ObjectValidation {
                // SecretKey is serialized as a string
                properties: [("SecretKey".to_string(), gen.subschema_for::<String>())]
                    .into_iter()
                    .collect(),
                required: ["SecretKey".to_string()].into_iter().collect(),
                ..Default::default()
            })),
            ..Default::default()
        };

        // This is the part that Schemars can't generate automatically:
        let untagged_array_schema = gen.subschema_for::<Array>();
        let untagged_set_schema = gen.subschema_for::<Set>();
        let untagged_dictionary_schema = gen.subschema_for::<Dictionary>();
        let untagged_string_schema = gen.subschema_for::<String>();
        let untagged_bool_schema = gen.subschema_for::<bool>();

        Schema::Object(SchemaObject {
            subschemas: Some(Box::new(schemars::schema::SubschemaValidation {
                any_of: Some(vec![
                    Schema::Object(root_schema),
                    Schema::Object(int_schema),
                    Schema::Object(raw_schema),
                    Schema::Object(public_key_schema),
                    Schema::Object(secret_key_schema),
                    untagged_array_schema,
                    untagged_dictionary_schema,
                    untagged_string_schema,
                    untagged_set_schema,
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
            TypedValue::Dictionary(d) => d.prove(&key.typed().try_into()?),
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
            TypedValue::Dictionary(d) => d.prove_nonexistence(&key.typed().try_into()?),
            TypedValue::Set(s) => s.prove_nonexistence(key),
            _ => Err(Error::custom(format!(
                "Invalid container value {}",
                self.typed()
            ))),
        }
    }
    /// Returns a Merkle state transition proof for inserting a
    /// key-value pair (if applicable).
    pub(crate) fn prove_insertion(
        &self,
        key: &Value,
        value: &Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let container = self.typed().clone();
        match container {
            TypedValue::Dictionary(mut d) => d.insert(&key.typed().try_into()?, value),
            TypedValue::Set(mut s) => s.insert(value),
            _ => Err(Error::custom(format!(
                "Invalid container value {}",
                self.typed()
            ))),
        }
    }
    /// Returns a Merkle state transition proof for updating a
    /// key-value pair (if applicable).
    pub(crate) fn prove_update(
        &self,
        key: &Value,
        value: &Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let container = self.typed().clone();
        match container {
            TypedValue::Array(mut a) => match key.typed() {
                TypedValue::Int(i) if i >= &0 => a.update(*i as usize, value),
                _ => Err(Error::custom(format!(
                    "Invalid key {} for container {}.",
                    key, self
                )))?,
            },
            TypedValue::Dictionary(mut d) => d.update(&key.typed().try_into()?, value),
            _ => Err(Error::custom(format!(
                "Invalid container value {} for update op",
                self.typed()
            ))),
        }
    }
    /// Returns a Merkle state transition proof for deleting a
    /// key (if applicable).
    pub(crate) fn prove_deletion(&self, key: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let container = self.typed().clone();
        match container {
            TypedValue::Dictionary(mut d) => d.delete(&key.typed().try_into()?),
            TypedValue::Set(mut s) => s.delete(key),
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

#[derive(Clone, Debug, Eq)]
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

impl hash::Hash for Key {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
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
        write!(f, "\"{}\"", self.name)?;
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

#[derive(Clone, Debug, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct AnchoredKey {
    pub root: Hash,
    pub key: Key,
}

impl AnchoredKey {
    pub fn new(root: Hash, key: Key) -> Self {
        Self { root, key }
    }
}

impl hash::Hash for AnchoredKey {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.root.hash(state);
        self.key.hash.hash(state);
    }
}

impl PartialEq for AnchoredKey {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root && self.key.hash == other.key.hash
    }
}

impl fmt::Display for AnchoredKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.root.fmt(f)?;
        write!(f, "[")?;
        self.key.fmt(f)?;
        write!(f, "]")?;
        Ok(())
    }
}

impl<T> From<(Hash, T)> for AnchoredKey
where
    T: Into<Key>,
{
    fn from((root, t): (Hash, T)) -> Self {
        Self::new(root, t.into())
    }
}

impl<T> From<(&Dictionary, T)> for AnchoredKey
where
    T: Into<Key>,
{
    fn from((dict, t): (&Dictionary, T)) -> Self {
        Self::new(dict.commitment(), t.into())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, FromRepr, Serialize, Deserialize, JsonSchema)]
pub enum PodType {
    Main = 1,
    Empty = 2,
    MockMain = 101,
    MockEmpty = 102,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::MockMain => write!(f, "MockMain"),
            PodType::MockEmpty => write!(f, "MockEmpty"),
            PodType::Main => write!(f, "Main"),
            PodType::Empty => write!(f, "Empty"),
        }
    }
}

/// Params: non dynamic parameters that define the circuit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema, Hash)]
#[serde(rename_all = "camelCase")]
pub struct Params {
    pub max_input_pods: usize,
    pub max_input_pods_public_statements: usize,
    pub max_statements: usize,
    pub max_public_statements: usize,
    pub max_operation_args: usize,
    // max number of custom predicates batches that a MainPod can use
    pub max_custom_predicate_batches: usize,
    // max number of operations using custom predicates that can be verified in the MainPod
    pub max_custom_predicate_verifications: usize,
    pub max_custom_predicate_wildcards: usize,
    // maximum number of merkle proofs used for container operations
    pub max_merkle_proofs_containers: usize,
    // maximum number of merkle tree state transition proofs used for container update operations
    pub max_merkle_tree_state_transition_proofs_containers: usize,
    // maximum depth for merkle tree gadget used for container operations
    pub max_depth_mt_containers: usize,
    // maximum depth of the merkle tree gadget used for verifier_data membership
    // check.  This allows creating verifying sets of pod circuits of size
    // 2^max_depth_mt_vds.  Limits the number of container operations of the type Contains,
    // NotContains.
    pub max_depth_mt_vds: usize,
    // maximum number of public key derivations used for PublicKeyOf operation
    pub max_public_key_of: usize,
    // maximum number of signature verifications used for SignedBy operation
    pub max_signed_by: usize,
    //
    // The following parameters define how a pod id is calculated.  They need to be the same among
    // different circuits to be compatible in their verification.
    //
    // Number of public statements to hash to calculate the public inputs.  Must be equal or
    // greater than `max_public_statements`.
    pub num_public_statements_hash: usize,
    pub max_statement_args: usize,
    //
    // The following parameters define how a custom predicate batch id is calculated.
    //
    // max number of statements that can be ANDed or ORed together
    // in a custom predicate
    pub max_custom_predicate_arity: usize,
    pub max_custom_batch_size: usize,
}

impl Default for Params {
    fn default() -> Self {
        Self {
            max_input_pods: 2,
            max_input_pods_public_statements: 10,
            max_statements: 40,
            max_public_statements: 10,
            num_public_statements_hash: 16,
            max_statement_args: 5,
            max_operation_args: 5,
            max_custom_predicate_batches: 2,
            max_custom_predicate_verifications: 5,
            max_custom_predicate_arity: 5,
            max_custom_predicate_wildcards: 10,
            max_custom_batch_size: 5, // TODO: Move down to 4?
            max_merkle_proofs_containers: 16,
            max_merkle_tree_state_transition_proofs_containers: 5,
            max_depth_mt_containers: 32,
            max_depth_mt_vds: 6, // up to 64 (2^6) different pod circuits
            max_public_key_of: 2,
            max_signed_by: 3,
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

    pub const fn statement_tmpl_size(&self) -> usize {
        Self::predicate_size() + self.max_statement_args * Self::statement_tmpl_arg_size()
    }

    pub fn custom_predicate_size(&self) -> usize {
        self.max_custom_predicate_arity * self.statement_tmpl_size() + 2
    }

    pub fn custom_predicate_batch_size_field_elts(&self) -> usize {
        self.max_custom_batch_size * self.custom_predicate_size()
    }

    /// Total size of the statement table including None, input statements from signed pods and
    /// input recursive pods and new statements (public & private)
    pub fn statement_table_size(&self) -> usize {
        1 + self.max_input_pods * self.max_input_pods_public_statements + self.max_statements
    }

    /// Parameters that define how the id is calculated
    pub fn id_params(&self) -> Vec<usize> {
        vec![
            self.num_public_statements_hash,
            self.max_statement_args,
            self.max_custom_predicate_arity,
            self.max_custom_batch_size,
        ]
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

/// Replace EMPTY_HASH in IntroPredicateRef by verifier_data_hash
pub fn normalize_statement(statement: &Statement, verifier_data_hash: Hash) -> Statement {
    match statement {
        Statement::Intro(ir, args) if ir.verifier_data_hash == EMPTY_HASH => Statement::Intro(
            IntroPredicateRef {
                name: ir.name.clone(),
                args_len: ir.args_len,
                verifier_data_hash,
            },
            args.clone(),
        ),
        s => s.clone(),
    }
}

pub trait EqualsAny {
    fn equals_any(&self, other: &dyn Any) -> bool;
}

impl<T: Any + Eq> EqualsAny for T {
    fn equals_any(&self, other: &dyn Any) -> bool {
        if let Some(o) = other.downcast_ref::<T>() {
            self == o
        } else {
            false
        }
    }
}

/// Trait for pods that are generated with a plonky2 circuit and that can be verified by a
/// recursive MainPod circuit (with the exception of mock types).  A Pod implementing this trait
/// does not necesarilly come from recursion: for example an introduction Pod in general is not
/// recursive.
pub trait Pod: fmt::Debug + DynClone + Sync + Send + Any + EqualsAny {
    fn params(&self) -> &Params;
    fn verify(&self) -> Result<(), BackendError>;
    /// Overwrite this method to return true in a mock pod to skip plonky2 verification
    fn is_mock(&self) -> bool {
        false
    }
    /// Overwrite this method to return true in a MainPod to generate verifier key inclusion proof
    /// into the vd set
    fn is_main(&self) -> bool {
        false
    }
    /// Hash of the public statements.  This can be used to identify a Pod.  Different pods can
    /// have the same `statements_hash` if they expose the same public statements even if they
    /// arrive to them through different private inputs.
    fn statements_hash(&self) -> Hash;
    // TODO: String instead of &str
    /// Return a uuid of the pod type and its name.  The name is only used as metadata.
    fn pod_type(&self) -> (usize, &'static str);
    /// Statements as internally generated, where self-referencing arguments use SELF in the
    /// anchored key.  The serialization of these statements is used to calculate the id.
    fn pub_self_statements(&self) -> Vec<Statement>;
    /// Normalized statements, where self-referencing arguments use the pod id instead of SELF in
    /// the anchored key.
    fn pub_statements(&self) -> Vec<Statement> {
        let verifier_data_hash = self.verifier_data_hash();
        self.pub_self_statements()
            .into_iter()
            .map(|statement| normalize_statement(&statement, verifier_data_hash))
            .collect()
    }
    /// Return this Pods data serialized into a json value.  This serialization can skip `params,
    /// id, vds_root`
    fn serialize_data(&self) -> serde_json::Value;

    /// Returns the deserialized Pod.
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        sts_hash: Hash,
    ) -> Result<Self, BackendError>
    where
        Self: Sized;

    fn equals(&self, other: &dyn Pod) -> bool {
        self.equals_any(other as &dyn Any)
    }

    fn verifier_data(&self) -> VerifierOnlyCircuitData;
    fn verifier_data_hash(&self) -> Hash {
        Hash(hash_verifier_data(&self.verifier_data()).elements)
    }
    /// Return a hash of the CommonCircuitData that uniquely identifies the circuit
    /// configuration and list of custom gates.
    fn common_hash(&self) -> String;
    fn proof(&self) -> Proof;
    fn vd_set(&self) -> &VDSet;
}
impl PartialEq for Box<dyn Pod> {
    fn eq(&self, other: &Self) -> bool {
        self.equals(&**other)
    }
}

impl Eq for Box<dyn Pod> {}

// impl Clone for Box<dyn Pod>
dyn_clone::clone_trait_object!(Pod);

pub trait Signer {
    fn sign(&self, msg: RawValue) -> Signature;
    fn public_key(&self) -> PublicKey;
}

#[derive(Debug)]
pub struct MainPodInputs<'a> {
    pub pods: &'a [&'a dyn Pod],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    /// Statements that need to be made public (they can come from input pods or input
    /// statements)
    pub public_statements: &'a [Statement],
    pub vd_set: VDSet,
}

pub trait MainPodProver {
    fn prove(&self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>, BackendError>;
}

pub trait ToFields {
    /// returns Vec<F> representation of the type
    fn to_fields(&self, params: &Params) -> Vec<F>;
}
