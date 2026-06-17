//! This file implements the types defined at
//! <https://0xparc.github.io/pod2/values.html#dictionary-array-set> .

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
    str::FromStr,
};

use schemars::JsonSchema;
use serde::{de::Error as _, ser, Deserialize, Deserializer, Serialize};

#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{self, MerkleProof, MerkleTree};
use crate::{
    backends::plonky2::primitives::merkletree::MerkleTreeStateTransitionProof,
    middleware::{
        db::{self, mem::MemDB, DB, TX},
        Error, Hash, RawValue, Result, StrKey, TypedValue, Value, EMPTY_HASH,
    },
};

pub const EMPTY_MT_ROOT: Hash = EMPTY_HASH;

/// Bitmask of container type.  We have three contianer types: Dictionary, Set and Array, and all
/// of them are backed up by a MerkleTree.  The three container types internally map to a key-value
/// where key is Value and value is Value, but they use different rules:
/// - The Dictionary uses String (as a Value) for the key
/// - The Array uses non-negative Int (as a Value) for the key
/// - The Set uses key = value
///
/// Because of this we can have containers that can be different types at the same time, for
/// example:
/// - Dict{"a": "a"} == Set{"a"}
/// - Dict{"a": "a", "b": "b"} = Set{"a", "b"}
/// - Array[0] == Set{0}
/// - Array[0, 1] = Set{0, 1}
/// - Dict{} == Array[] == Set{}
///
/// For this reason we use a bitmask for the generic Container to flag what kind of container type
/// it can be used as.  Usually only one bit will be set, but in the case of an edge case like the
/// ones above, multiple bits will be set.
///
/// When using a persistent database we store this container indexed by the root of the container,
/// and we update it to store all the container types seen for each root by ORing the mask so that
/// no information is lost.
///
/// The string encoding of this bitmask contains three characters which are `d,s,a` or `-`
/// depending on whether the bit flag is set or not for each of Dictionary, Set and Array.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ContainerKind(pub(crate) u8);

impl ContainerKind {
    pub fn is_dictionary(&self) -> bool {
        self.0 & (1 << 0) != 0
    }
    pub fn is_set(&self) -> bool {
        self.0 & (1 << 1) != 0
    }
    pub fn is_array(&self) -> bool {
        self.0 & (1 << 2) != 0
    }
    pub(crate) fn set_dictionary(&mut self) -> &mut Self {
        self.0 |= 1 << 0;
        self
    }
    pub(crate) fn set_set(&mut self) -> &mut Self {
        self.0 |= 1 << 1;
        self
    }
    pub(crate) fn set_array(&mut self) -> &mut Self {
        self.0 |= 1 << 2;
        self
    }
}

impl FromStr for ContainerKind {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        let s = s.as_bytes();
        if s.len() != 3 {
            return Err(Error::custom("invalid length"));
        }
        let mut kind = Self::default();
        if s[0] == b'd' {
            kind.set_dictionary();
        } else if s[0] != b'-' {
            return Err(Error::custom("invalid char at pos 0"));
        }
        if s[1] == b's' {
            kind.set_set();
        } else if s[1] != b'-' {
            return Err(Error::custom("invalid char at pos 1"));
        }
        if s[2] == b'a' {
            kind.set_array();
        } else if s[2] != b'-' {
            return Err(Error::custom("invalid char at pos 2"));
        }
        Ok(kind)
    }
}

impl fmt::Display for ContainerKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.is_dictionary() {
            true => write!(f, "d")?,
            false => write!(f, "-")?,
        }
        match self.is_set() {
            true => write!(f, "s")?,
            false => write!(f, "-")?,
        }
        match self.is_array() {
            true => write!(f, "a")?,
            false => write!(f, "-")?,
        }
        Ok(())
    }
}

impl JsonSchema for ContainerKind {
    fn schema_name() -> String {
        "ContainerKind".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        String::json_schema(gen)
    }
}

impl Serialize for ContainerKind {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&format!("{}", self))
    }
}

impl<'de> Deserialize<'de> for ContainerKind {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        ContainerKind::from_str(&s)
            .map_err(|e| D::Error::custom(format!("invalid encoding of ContainerKind {e}")))
    }
}

#[derive(Clone, Debug)]
pub struct Container {
    pub(crate) kind: ContainerKind,
    root: Hash,
    db: Box<dyn DB>,
}

#[derive(Serialize, Deserialize, JsonSchema)]
struct SerializedContainer {
    kind: ContainerKind,
    kvs: Vec<Vec<Value>>,
}

impl JsonSchema for Container {
    fn schema_name() -> String {
        "Container".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        SerializedContainer::json_schema(gen)
    }
}

impl Serialize for Container {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut pairs = self
            .iter()
            .map(|result_pair| result_pair.map(|(k, v)| if k == v { vec![v] } else { vec![k, v] }))
            .collect::<Result<Vec<Vec<Value>>>>()
            .map_err(ser::Error::custom)?;
        pairs.sort_by(|pair_l, pair_r| pair_l[0].raw().cmp(&pair_r[0].raw()));
        SerializedContainer {
            kind: self.kind,
            kvs: pairs,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Container {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let c = SerializedContainer::deserialize(deserializer)?;
        let is_dictionary = c.kind.is_dictionary();
        let is_set = c.kind.is_set();
        let is_array = c.kind.is_array();
        let mut kvs = HashMap::<Value, Value>::new();
        for mut elem in c.kvs {
            let Some(key) = elem.first() else {
                return Err(D::Error::custom(
                    "invalid container: elem.length() = 0".to_string(),
                ));
            };
            // Type validation
            if is_set && elem.len() != 1 {
                return Err(D::Error::custom("not a set: elem.len != 1"));
            }
            if is_array && !matches!(&key.typed, TypedValue::Int(i) if *i >= 0) {
                return Err(D::Error::custom("not an array: non-index key"));
            }
            if is_dictionary && !matches!(&key.typed, TypedValue::String(_)) {
                return Err(D::Error::custom("not a dictionary: non-string key"));
            }
            match elem.len() {
                1 => {
                    let v = elem.pop().unwrap();
                    kvs.insert(v.clone(), v);
                }
                2 => {
                    let (v, k) = (elem.pop().unwrap(), elem.pop().unwrap());
                    kvs.insert(k, v);
                }
                n => {
                    return Err(D::Error::custom(format!(
                        "invalid vec length of {n} in container entry"
                    )))
                }
            }
        }
        Ok(Container::new(c.kind, kvs))
    }
}

// Validate inner container type during deserialization.

impl<'de> Deserialize<'de> for Set {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut inner = Container::deserialize(deserializer)?;
        if !inner.kind.is_set() {
            return Err(D::Error::custom("container not a set"));
        }
        inner.kind = *ContainerKind::default().set_set();
        Ok(Set { inner })
    }
}

impl<'de> Deserialize<'de> for Dictionary {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut inner = Container::deserialize(deserializer)?;
        if !inner.kind.is_dictionary() {
            return Err(D::Error::custom("container not a dictionary"));
        }
        inner.kind = *ContainerKind::default().set_dictionary();
        Ok(Dictionary { inner })
    }
}

impl<'de> Deserialize<'de> for Array {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let mut inner = Container::deserialize(deserializer)?;
        if !inner.kind.is_array() {
            return Err(D::Error::custom("container not an array"));
        }
        inner.kind = *ContainerKind::default().set_array();
        Ok(Array { inner })
    }
}

impl PartialEq for Container {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
    }
}
impl Eq for Container {}

fn store_container_mt(tx: &mut dyn TX, container: &Container) -> Result<()> {
    match tx.load_node(container.root) {
        Err(e) => return Err(Error::Database(e)),
        // Container already exists in the DB
        Ok(Some(_)) => return Ok(()),
        // Container not existing, we need to save it
        Ok(None) => {}
    };
    let mut root = EMPTY_HASH;
    for kv_result in container.iter() {
        let (k, v) = kv_result?;
        let mtp = insert_tx(tx, root, k, v)?;
        root = mtp.new_root;
    }
    Ok(())
}

fn store_value(tx: &mut dyn TX, v: Value) -> Result<()> {
    match &v.typed {
        TypedValue::Container(inner) if tx.is_persistent() => store_container_mt(tx, inner)?,
        _ => tx.store_value(v).map_err(Error::Database)?,
    }
    Ok(())
}

fn load_value(db: &dyn db::DB, value_raw: RawValue) -> Result<Value> {
    match db.load_value(value_raw) {
        Err(e) => Err(Error::Database(e)),
        Ok(Some(v)) => Ok(v),
        Ok(None) => {
            // With a persistent DB we skip storing containers as values and instead store them as
            // merkle trees via the Container type.
            if db.is_persistent() {
                if let Ok(c) = Container::from_db(Hash(value_raw.0), db.clone_box()) {
                    return Ok(Value::from(c));
                }
            }
            Err(Error::custom(format!(
                "Value from {value_raw} not found in DB"
            )))
        }
    }
}

fn insert_tx(
    tx: &mut dyn TX,
    root: Hash,
    key: Value,
    value: Value,
) -> Result<MerkleTreeStateTransitionProof> {
    let (key_raw, value_raw) = (key.raw(), value.raw());
    store_value(tx, key)?;
    store_value(tx, value)?;
    let mtp = merkletree::insert_tx(tx, root, &key_raw, &value_raw)?;
    Ok(mtp)
}

impl Container {
    pub fn kind(&self) -> ContainerKind {
        self.kind
    }
    pub fn mt(&self) -> MerkleTree {
        MerkleTree::from_db(self.root, self.db.clone())
    }
    fn new(kind: ContainerKind, kvs: HashMap<Value, Value>) -> Self {
        let db = Box::new(MemDB::new());
        let mut container = Self::empty_with_db(db);
        for (k, v) in kvs {
            container.insert(k, v).expect("no duplicates, no db errors");
        }
        container.kind = kind;
        container
    }
    fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self::from_db(EMPTY_HASH, db).expect("EMPTY_HASH exists implicitly")
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        // Make sure the root exists in the db
        let _ = merkletree::load_node(db.as_ref(), root)?;
        let kind = db
            .load_kind(root)
            .map_err(Error::Database)?
            .ok_or_else(|| Error::custom("container kind not found"))?;
        Ok(Self { kind, root, db })
    }
    pub fn commitment(&self) -> Hash {
        self.root
    }
    pub fn get(&self, key_raw: RawValue) -> Result<Option<Value>> {
        Ok(match self.mt().get(&key_raw)? {
            Some(value_raw) => Some(load_value(self.db.as_ref(), value_raw)?),
            None => None,
        })
    }
    pub fn prove(&self, key_raw: RawValue) -> Result<(Value, MerkleProof)> {
        let (value_raw, mtp) = self.mt().prove(&key_raw)?;
        let value = load_value(self.db.as_ref(), value_raw)?;
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key_raw: RawValue) -> Result<MerkleProof> {
        Ok(self.mt().prove_nonexistence(&key_raw)?)
    }
    fn insert(&mut self, key: Value, value: Value) -> Result<MerkleTreeStateTransitionProof> {
        let mut tx = DB::tx(self.db.as_ref());
        let mtp = insert_tx(tx.as_mut(), self.root, key, value)?;
        tx.update_kind(mtp.new_root, self.kind)
            .map_err(Error::Database)?;
        TX::commit(tx).map_err(Error::Database)?;
        self.root = mtp.new_root;
        Ok(mtp)
    }
    pub fn insert_proof(&self, key: Value, value: Value) -> Result<MerkleTreeStateTransitionProof> {
        let mut container = self.clone();
        container.insert(key, value)
    }
    fn update(
        &mut self,
        key_raw: RawValue,
        value: Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let value_raw = value.raw();
        let mut tx = DB::tx(self.db.as_ref());
        store_value(tx.as_mut(), value)?;
        let mtp = merkletree::update_tx(tx.as_mut(), self.root, &key_raw, &value_raw)?;
        tx.update_kind(mtp.new_root, self.kind)
            .map_err(Error::Database)?;
        TX::commit(tx).map_err(Error::Database)?;
        self.root = mtp.new_root;
        Ok(mtp)
    }
    pub fn update_proof(
        &self,
        key_raw: RawValue,
        value: Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let mut container = self.clone();
        container.update(key_raw, value)
    }
    fn delete(&mut self, key_raw: RawValue) -> Result<MerkleTreeStateTransitionProof> {
        let mut tx = DB::tx(self.db.as_ref());
        let mtp = merkletree::delete_tx(tx.as_mut(), self.root, &key_raw)?;
        tx.update_kind(mtp.new_root, self.kind)
            .map_err(Error::Database)?;
        TX::commit(tx).map_err(Error::Database)?;
        self.root = mtp.new_root;
        Ok(mtp)
    }
    pub fn delete_proof(&self, key_raw: RawValue) -> Result<MerkleTreeStateTransitionProof> {
        let mut container = self.clone();
        container.delete(key_raw)
    }
    pub fn verify(
        root: Hash,
        proof: &MerkleProof,
        key_raw: RawValue,
        value_raw: RawValue,
    ) -> Result<()> {
        Ok(merkletree::verify(root, proof, &key_raw, &value_raw)?)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key_raw: RawValue) -> Result<()> {
        Ok(merkletree::verify_nonexistence(root, proof, &key_raw)?)
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        merkletree::verify_state_transition(proof).map_err(|e| e.into())
    }
    pub fn iter(&self) -> impl Iterator<Item = Result<(Value, Value)>> {
        let db = self.db.clone();
        self.mt().iter().map(move |(key_raw, value_raw)| {
            let key = load_value(db.as_ref(), key_raw)?;
            let value = load_value(db.as_ref(), value_raw)?;
            Ok((key, value))
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashMap<Value, Value>> {
        self.iter().collect()
    }
    /// Casting methods narrow the kind in the container so that future write operations only
    /// record future container roots as that particular kind.
    pub fn as_dictionary(&self) -> Option<Dictionary> {
        if self.kind.is_dictionary() {
            let mut inner = self.clone();
            inner.kind = *ContainerKind::default().set_dictionary();
            Some(Dictionary { inner })
        } else {
            None
        }
    }
    pub fn as_set(&self) -> Option<Set> {
        if self.kind.is_set() {
            let mut inner = self.clone();
            inner.kind = *ContainerKind::default().set_set();
            Some(Set { inner })
        } else {
            None
        }
    }
    pub fn as_array(&self) -> Option<Array> {
        if self.kind.is_array() {
            let mut inner = self.clone();
            inner.kind = *ContainerKind::default().set_array();
            Some(Array { inner })
        } else {
            None
        }
    }
}

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Dictionary {
    pub(crate) inner: Container,
}

#[macro_export]
macro_rules! dict {
    ({ $($key:expr => $val:expr),* , }) => (
        $crate::dict!({ $($key => $val),* })
    );
    ({ $($key:expr => $val:expr),* }) => ({
        let mut map = ::std::collections::HashMap::new();
        $( map.insert($crate::middleware::StrKey::from($key), $crate::middleware::Value::from($val)); )*
        $crate::middleware::containers::Dictionary::new(map)
    });
}

// TODO: Replace all methods that receive a `&StrKey` by either `impl Into<String>` for write
// methods and `impl AsRef<str>` for read methods.
// TODO: Replace all methods that receive a `&Value` in write methods for `Value`.  Consider a
// trait?

impl Dictionary {
    pub fn new(kvs: HashMap<StrKey, Value>) -> Self {
        Self {
            inner: Container::new(
                *ContainerKind::default().set_dictionary(),
                kvs.into_iter()
                    .map(|(k, v)| (Value::from(k.into_name()), v))
                    .collect(),
            ),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Container::empty_with_db(db)
            .as_dictionary()
            .expect("empty container can be anything")
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Container::from_db(root, db)?
            .as_dictionary()
            .ok_or_else(|| Error::custom("not a dictionary"))
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn get(&self, key: &StrKey) -> Result<Option<Value>> {
        self.inner.get(key.raw())
    }
    pub fn prove(&self, key: &StrKey) -> Result<(Value, MerkleProof)> {
        self.inner.prove(key.raw())
    }
    pub fn prove_nonexistence(&self, key: &StrKey) -> Result<MerkleProof> {
        self.inner.prove_nonexistence(key.raw())
    }
    pub fn insert(
        &mut self,
        key: &StrKey,
        value: &Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        self.inner
            .insert(Value::from(key.name().to_string()), value.clone())
    }
    pub fn update(
        &mut self,
        key: &StrKey,
        value: &Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.update(key.raw(), value.clone())
    }
    pub fn delete(&mut self, key: &StrKey) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.delete(key.raw())
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &StrKey, value: &Value) -> Result<()> {
        Container::verify(root, proof, key.raw(), value.raw())
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &StrKey) -> Result<()> {
        Container::verify_nonexistence(root, proof, key.raw())
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        Container::verify_state_transition(proof)
    }
    pub fn iter(&self) -> impl Iterator<Item = Result<(String, Value)>> + use<'_> {
        self.inner.iter().map(|r| match r {
            Ok((key, value)) => Ok((
                key.as_string()
                    .ok_or_else(|| Error::custom("dictionary: key is not string"))?,
                value,
            )),
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashMap<String, Value>> {
        self.iter().collect()
    }
}

impl PartialEq for Dictionary {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}
impl Eq for Dictionary {}

/// Set: the value field of the leaf is unused, and the key contains the hash of the element.
///    leaf.key=hash(original_value)
///    leaf.value=0
#[derive(Clone, Debug, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Set {
    pub(crate) inner: Container,
}

impl Set {
    pub fn new(set: HashSet<Value>) -> Self {
        Self {
            inner: Container::new(
                *ContainerKind::default().set_set(),
                set.into_iter().map(|v| (v.clone(), v)).collect(),
            ),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Container::empty_with_db(db)
            .as_set()
            .expect("empty container can be anything")
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Container::from_db(root, db)?
            .as_set()
            .ok_or_else(|| Error::custom("not a set"))
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn contains(&self, value: &Value) -> Result<bool> {
        Ok(self.inner.get(value.raw())?.is_some())
    }
    pub fn prove(&self, value: &Value) -> Result<MerkleProof> {
        let (_, proof) = self.inner.prove(value.raw())?;
        Ok(proof)
    }
    pub fn prove_nonexistence(&self, value: &Value) -> Result<MerkleProof> {
        self.inner.prove_nonexistence(value.raw())
    }
    pub fn insert(&mut self, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.insert(value.clone(), value.clone())
    }
    pub fn delete(&mut self, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.delete(value.raw())
    }
    pub fn verify(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        Container::verify(root, proof, value.raw(), value.raw())
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        Container::verify_nonexistence(root, proof, value.raw())
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        Container::verify_state_transition(proof)
    }
    pub fn iter(&self) -> impl Iterator<Item = Result<Value>> + use<'_> {
        self.inner.iter().map(|r| match r {
            Ok((key, value)) => {
                if key != value {
                    return Err(Error::custom("set: key != value"));
                }
                Ok(value)
            }
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashSet<Value>> {
        self.iter().collect()
    }
}

impl PartialEq for Set {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}
impl Eq for Set {}

/// Array: the elements are placed at the value field of each leaf, and the key field is just the
/// array index (integer).
///    leaf.key=i
///    leaf.value=original_value
/// Due to its construction this should be seen as a sparse array, where there can be gaps
/// (unused indices).
#[derive(Clone, Debug, Serialize, JsonSchema)]
#[serde(transparent)]
pub struct Array {
    pub(crate) inner: Container,
}

impl Array {
    pub fn new(array: Vec<Value>) -> Self {
        Self {
            inner: Container::new(
                *ContainerKind::default().set_array(),
                array
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| (Value::from(i as i64), v))
                    .collect(),
            ),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Container::empty_with_db(db)
            .as_array()
            .expect("empty container can be anything")
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Container::from_db(root, db)?
            .as_array()
            .ok_or_else(|| Error::custom("not an array"))
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn get(&self, i: usize) -> Result<Option<Value>> {
        self.inner.get(Value::from(i as i64).raw())
    }
    pub fn prove(&self, i: usize) -> Result<(Value, MerkleProof)> {
        self.inner.prove(Value::from(i as i64).raw())
    }
    pub fn insert(&mut self, i: usize, value: Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.insert(Value::from(i as i64), value)
    }
    pub fn delete(&mut self, i: usize) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.delete(Value::from(i as i64).raw())
    }
    pub fn update(&mut self, i: usize, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner
            .update(Value::from(i as i64).raw(), value.clone())
    }
    pub fn verify(root: Hash, proof: &MerkleProof, i: usize, value: &Value) -> Result<()> {
        Container::verify(root, proof, Value::from(i as i64).raw(), value.raw())
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        Container::verify_state_transition(proof)
    }
    pub fn iter(&self) -> impl Iterator<Item = Result<(usize, Value)>> + use<'_> {
        self.inner.iter().map(|r| match r {
            Ok((key, value)) => {
                let index = key
                    .as_int()
                    .ok_or_else(|| Error::custom("array: key is not int"))?;
                Ok((index as usize, value))
            }
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashMap<usize, Value>> {
        self.iter().collect()
    }
}

impl PartialEq for Array {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}
impl Eq for Array {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::middleware::db::mem::MemDB;

    #[test]
    fn value_serde_round_trip_preserves_container_kind() {
        let dict = Value::from(Dictionary::new(
            [(StrKey::from("score"), Value::from(42))].into(),
        ));
        let array = Value::from(Array::new(vec![Value::from(10), Value::from("x")]));
        let set = Value::from(Set::new(HashSet::from([Value::from(7)])));
        let nested = Value::from(Dictionary::new(
            [(
                StrKey::from("items"),
                Value::from(Array::new(vec![Value::from(1)])),
            )]
            .into(),
        ));
        let empty_dict = Value::from(Dictionary::new([].into()));
        let empty_array = Value::from(Array::new(vec![]));
        // Sets always have identical keys and values, so this example is
        // used to check that a dict which happens to have key=value is not
        // mistakenly interpreted as a set.
        let self_keyed_dict = Value::from(Dictionary::new(
            [(StrKey::from("a"), Value::from("a"))].into(),
        ));
        let identity_array = Value::from(Array::new(vec![Value::from(0), Value::from(1)]));

        for value in [
            dict,
            array,
            set,
            nested,
            empty_dict,
            empty_array,
            self_keyed_dict,
            identity_array,
        ] {
            let json = serde_json::to_string(&value).unwrap();
            let back: Value = serde_json::from_str(&json).unwrap();
            assert_eq!(back.raw(), value.raw(), "raw mismatch for {value}");
            assert_eq!(
                std::mem::discriminant(&back.typed),
                std::mem::discriminant(&value.typed),
                "kind mismatch: {value} came back as {back}"
            );
        }
    }

    fn test_databases(test_fn: &dyn Fn(Box<dyn DB>)) {
        let db = MemDB::new();
        test_fn(Box::new(db));
        #[cfg(feature = "db_rocksdb")]
        {
            use crate::middleware::db;
            let db = db::rocks::RocksDB::open(tempfile::TempDir::new().unwrap().path()).unwrap();
            test_fn(Box::new(db));
        }
    }

    fn _test_dict(db: Box<dyn DB>) {
        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0.insert(&StrKey::from("a"), &Value::from(1)).unwrap();
        dict0.insert(&StrKey::from("b"), &Value::from(2)).unwrap();
        dict0.update(&StrKey::from("a"), &Value::from(3)).unwrap();
        dict0.insert(&StrKey::from("c"), &Value::from(4)).unwrap();
        dict0.delete(&StrKey::from("c")).unwrap();
        let kvs0 = dict0.dump().unwrap();
        assert_eq!(
            kvs0,
            [
                ("a".to_string(), Value::from(3)),
                ("b".to_string(), Value::from(2))
            ]
            .into_iter()
            .collect()
        );
        let dict1 = Dictionary::from_db(dict0.commitment(), db).unwrap();
        let kvs1 = dict1.dump().unwrap();
        assert_eq!(kvs0, kvs1);
    }

    fn _test_set(db: Box<dyn DB>) {
        let mut set0 = Set::empty_with_db(db.clone());
        set0.insert(&Value::from(1)).unwrap();
        set0.insert(&Value::from(2)).unwrap();
        set0.insert(&Value::from(3)).unwrap();
        set0.delete(&Value::from(2)).unwrap();

        let s0 = set0.dump().unwrap();
        assert_eq!(s0, [Value::from(1), Value::from(3)].into_iter().collect());
        let set1 = Set::from_db(set0.commitment(), db).unwrap();
        let s1 = set1.dump().unwrap();
        assert_eq!(s0, s1);
    }

    fn _test_array(db: Box<dyn DB>) {
        let mut arr0 = Array::empty_with_db(db.clone());
        arr0.insert(0, Value::from("a")).unwrap();
        arr0.insert(1, Value::from("b")).unwrap();
        arr0.insert(2, Value::from("c")).unwrap();
        arr0.delete(1).unwrap();

        let a0 = arr0.dump().unwrap();
        assert_eq!(
            a0,
            [(0, Value::from("a")), (2, Value::from("c"))]
                .into_iter()
                .collect()
        );
        let arr1 = Array::from_db(arr0.commitment(), db).unwrap();
        let a1 = arr1.dump().unwrap();
        assert_eq!(a0, a1);
    }

    fn _test_nested(db: Box<dyn DB>) {
        let mut nested = Dictionary::empty_with_db(db.clone());
        nested.insert(&StrKey::from("a"), &Value::from(1)).unwrap();
        nested.insert(&StrKey::from("b"), &Value::from(2)).unwrap();
        let nested_kvs0 = nested.dump().unwrap();

        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0.insert(&StrKey::from("x"), &Value::from(1)).unwrap();
        dict0
            .insert(&StrKey::from("y"), &Value::from(nested.clone()))
            .unwrap();
        let kvs0 = dict0.dump().unwrap();

        assert_eq!(
            kvs0,
            [
                ("x".to_string(), Value::from(1)),
                ("y".to_string(), Value::from(nested))
            ]
            .into_iter()
            .collect()
        );

        let dict1 = Dictionary::from_db(dict0.commitment(), db).unwrap();
        let kvs1 = dict1.dump().unwrap();
        assert_eq!(kvs0, kvs1);

        match &kvs1["y"].typed {
            TypedValue::Container(d) => {
                let nested_kvs1 = d.as_dictionary().unwrap().dump().unwrap();
                assert_eq!(nested_kvs0, nested_kvs1);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_dict() {
        test_databases(&_test_dict);
    }

    #[test]
    fn test_set() {
        test_databases(&_test_set);
    }

    #[test]
    fn test_array() {
        test_databases(&_test_array);
    }

    #[test]
    fn test_nested() {
        test_databases(&_test_nested);
    }

    #[test]
    fn test_empty() {
        assert_eq!(EMPTY_MT_ROOT, Array::new(Vec::new()).commitment());
        assert_eq!(EMPTY_MT_ROOT, Set::new(HashSet::new()).commitment());
        assert_eq!(EMPTY_MT_ROOT, Dictionary::new(HashMap::new()).commitment());
    }

    #[test]
    fn same_roots() {
        let mut a = Dictionary::new(HashMap::new());
        a.insert(&StrKey::new("a".to_string()), &Value::from("a".to_string()))
            .unwrap();
        let a = Value::from(a);
        let mut b = Set::new(HashSet::new());
        b.insert(&Value::from("a".to_string())).unwrap();
        let b = Value::from(b);
        println!("a: {}", serde_json::to_string(&a).unwrap());
        println!("b: {}", serde_json::to_string(&b).unwrap());
        let top = Array::new(vec![a, b]);
        let top_json = serde_json::to_string(&top).unwrap();
        println!("top: {}", top_json);
        assert_eq!(
            top_json,
            r#"{"kind":"--a","kvs":[[{"Int":"0"},{"Container":{"kind":"ds-","kvs":[["a"]]}}],[{"Int":"1"},{"Container":{"kind":"ds-","kvs":[["a"]]}}]]}"#
        );
    }

    fn _test_kind(db: Box<dyn DB>) {
        let mut nested_dict = Dictionary::empty_with_db(db.clone());
        nested_dict
            .insert(&StrKey::from("a"), &Value::from("a"))
            .unwrap();
        nested_dict
            .insert(&StrKey::from("b"), &Value::from("b"))
            .unwrap();

        assert!(nested_dict.inner.kind.is_dictionary());
        assert!(!nested_dict.inner.kind.is_set());
        assert!(!nested_dict.inner.kind.is_array());

        // Only observed the container as a Dictionary, not a Set
        assert!(Dictionary::from_db(nested_dict.commitment(), db.clone()).is_ok());
        assert!(Set::from_db(nested_dict.commitment(), db.clone()).is_err());

        let mut nested_set = Set::empty_with_db(db.clone());
        nested_set.insert(&Value::from("a")).unwrap();
        nested_set.insert(&Value::from("b")).unwrap();

        // We intentionally made a collision
        assert_eq!(nested_dict.commitment(), nested_set.commitment());

        // Observed the container both as a Dictionary and a Set
        assert!(Dictionary::from_db(nested_dict.commitment(), db.clone()).is_ok());
        assert!(Set::from_db(nested_dict.commitment(), db.clone()).is_ok());

        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0
            .insert(&StrKey::from("x"), &Value::from(nested_dict))
            .unwrap();
        dict0
            .insert(&StrKey::from("y"), &Value::from(nested_set.clone()))
            .unwrap();

        assert!(dict0
            .get(&StrKey::from("x"))
            .unwrap()
            .unwrap()
            .as_dictionary()
            .is_some());
        assert!(dict0
            .get(&StrKey::from("y"))
            .unwrap()
            .unwrap()
            .as_set()
            .is_some());
    }

    #[test]
    fn test_kind() {
        test_databases(&_test_kind);
    }
}
