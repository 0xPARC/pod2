//! This file implements the types defined at
//! <https://0xparc.github.io/pod2/values.html#dictionary-array-set> .

#![allow(unused_imports)] // TODO: Remove

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Debug,
    sync::{Arc, RwLock},
};

use anyhow::bail;
use dyn_clone::{clone_box, DynClone};
use schemars::JsonSchema;
use serde::{de, ser, Deserialize, Deserializer, Serialize};

use super::serialization::{ordered_map, ordered_set};
#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{self, MerkleProof, MerkleTree, TreeError};
use crate::{
    backends::plonky2::primitives::merkletree::MerkleTreeStateTransitionProof,
    middleware::{
        db::{mem::MemDB, DB},
        hash_str, Error, Hash, Key, RawValue, Result, TypedValue, Value, EMPTY_HASH, EMPTY_VALUE,
    },
};

#[derive(Clone, Debug)]
pub struct Container {
    root: Hash,
    db: Box<dyn DB>,
}

impl JsonSchema for Container {
    fn schema_name() -> String {
        "Container".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        // Just use the schema of HashMap<Value, Value> since that's what we're actually serializing
        HashMap::<Value, Value>::json_schema(gen)
    }
}

impl Serialize for Container {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut pairs = self
            .iter()
            .collect::<Result<Vec<(Value, Value)>>>()
            .map_err(ser::Error::custom)?;
        pairs.sort_by(|(k1, _), (k2, _)| k1.raw().cmp(&k2.raw()));
        // Serialize as a map
        use serde::ser::SerializeMap;
        let mut map = serializer.serialize_map(Some(pairs.len()))?;
        for (k, v) in pairs {
            map.serialize_entry(&k, &v)?;
        }
        map.end()
    }
}

impl<'de> Deserialize<'de> for Container {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let kvs = HashMap::<Value, Value>::deserialize(deserializer)?;
        Ok(Container::new(kvs))
    }
}

impl PartialEq for Container {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
    }
}
impl Eq for Container {}

fn store_container_mt(db: &mut dyn DB, container: &Container) -> Result<()> {
    match db.load_node(container.root) {
        Err(e) => return Err(Error::Database(e)),
        // Container already exists in the DB
        Ok(Some(_)) => return Ok(()),
        // Container not existing, we need to save it
        Ok(None) => {}
    };
    let mut container_copy = Container::empty_with_db(db.clone_box());
    for kv_result in container.iter() {
        let (k, v) = kv_result?;
        container_copy.insert(k, v)?;
    }
    Ok(())
}

fn store_value(db: &mut dyn DB, v: Value) -> Result<()> {
    match v.typed() {
        TypedValue::Set(Set { inner })
        | TypedValue::Dictionary(Dictionary { inner })
        | TypedValue::Array(Array { inner }) => {
            if db.is_persistent() {
                store_container_mt(db, inner)?;
            }
            db.store_value(v).map_err(Error::Database)?
        }
        _ => db.store_value(v).map_err(Error::Database)?,
    }
    Ok(())
}

fn load_value(db: &dyn DB, value_raw: RawValue) -> Result<Value> {
    match db.load_value(value_raw) {
        Err(e) => Err(Error::Database(e)),
        Ok(Some(v)) => Ok(v),
        Ok(None) => Err(Error::custom(format!(
            "Value from {value_raw} not found in DB"
        ))),
    }
}

impl Container {
    fn mt(&self) -> MerkleTree {
        MerkleTree::from_db(self.root, self.db.clone())
    }
    pub fn new(kvs: HashMap<Value, Value>) -> Self {
        let db = Box::new(MemDB::new());
        let mut container = Self::empty_with_db(db);
        for (k, v) in kvs {
            container.insert(k, v).expect("no duplicates, no db errors");
        }
        container
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self::from_db(EMPTY_HASH, db).expect("EMPTY_HASH exists implicitly")
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        // Make sure the root exists in the db
        let _ = merkletree::load_node(db.as_ref(), root)?;
        Ok(Self { root, db })
    }
    pub fn commitment(&self) -> Hash {
        self.root
    }
    pub fn get(&self, key_raw: RawValue) -> Result<Value> {
        let value_raw = self.mt().get(&key_raw)?;
        let value = load_value(self.db.as_ref(), value_raw)?;
        Ok(value)
    }
    pub fn prove(&self, key_raw: RawValue) -> Result<(Value, MerkleProof)> {
        let (value_raw, mtp) = self.mt().prove(&key_raw)?;
        let value = load_value(self.db.as_ref(), value_raw)?;
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key_raw: RawValue) -> Result<MerkleProof> {
        Ok(self.mt().prove_nonexistence(&key_raw)?)
    }
    pub fn insert(&mut self, key: Value, value: Value) -> Result<MerkleTreeStateTransitionProof> {
        let (key_raw, value_raw) = (key.raw(), value.raw());
        store_value(self.db.as_mut(), key)?;
        store_value(self.db.as_mut(), value)?;
        let mut mt = self.mt();
        let mtp = mt.insert(&key_raw, &value_raw)?;
        self.root = mt.root();
        Ok(mtp)
    }
    pub fn update(
        &mut self,
        key_raw: RawValue,
        value: Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let value_raw = value.raw();
        store_value(self.db.as_mut(), value).unwrap();
        let mut mt = self.mt();
        let mtp = mt.update(&key_raw, &value_raw)?;
        self.root = mt.root();
        Ok(mtp)
    }
    pub fn delete(&mut self, key_raw: RawValue) -> Result<MerkleTreeStateTransitionProof> {
        let mut mt = self.mt();
        let mtp = mt.delete(&key_raw)?;
        self.root = mt.root();
        Ok(mtp)
    }
    pub fn verify(
        root: Hash,
        proof: &MerkleProof,
        key_raw: RawValue,
        value_raw: RawValue,
    ) -> Result<()> {
        Ok(MerkleTree::verify(root, proof, &key_raw, &value_raw)?)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key_raw: RawValue) -> Result<()> {
        Ok(MerkleTree::verify_nonexistence(root, proof, &key_raw)?)
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        MerkleTree::verify_state_transition(proof).map_err(|e| e.into())
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
        self.iter().map(|kv| kv).collect()
    }
}

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
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
        $( map.insert($crate::middleware::Key::from($key), $crate::middleware::Value::from($val)); )*
        $crate::middleware::containers::Dictionary::new(map)
    });
}

// TODO: Replace all methods that receive a `&Key` by either `impl Into<String>` for write
// methods and `impl AsRef<str>` for read methods.
// TODO: Replace all methods that receive a `&Value` in write methods for `Value`.  Consider a
// trait?

impl Dictionary {
    pub fn new(kvs: HashMap<Key, Value>) -> Self {
        Self {
            inner: Container::new(
                kvs.into_iter()
                    .map(|(k, v)| (Value::from(k.name), v))
                    .collect(),
            ),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::empty_with_db(db),
        }
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Ok(Self {
            inner: Container::from_db(root, db)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn get(&self, key: &Key) -> Result<Value> {
        self.inner.get(key.raw())
    }
    pub fn prove(&self, key: &Key) -> Result<(Value, MerkleProof)> {
        self.inner.prove(key.raw())
    }
    pub fn prove_nonexistence(&self, key: &Key) -> Result<MerkleProof> {
        self.inner.prove_nonexistence(key.raw())
    }
    pub fn insert(&mut self, key: &Key, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner
            .insert(Value::from(key.name.clone()), value.clone())
    }
    pub fn update(&mut self, key: &Key, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.update(key.raw(), value.clone())
    }
    pub fn delete(&mut self, key: &Key) -> Result<MerkleTreeStateTransitionProof> {
        self.inner.delete(key.raw())
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &Key, value: &Value) -> Result<()> {
        Container::verify(root, proof, key.raw(), value.raw())
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &Key) -> Result<()> {
        Container::verify_nonexistence(root, proof, key.raw())
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        Container::verify_state_transition(proof)
    }
    pub fn iter(&self) -> impl Iterator<Item = Result<(String, Value)>> + use<'_> {
        self.inner.iter().map(|r| match r {
            Ok((key, value)) => Ok((String::try_from(key.typed())?, value)),
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashMap<String, Value>> {
        self.iter().map(|kv| kv).collect()
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
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Set {
    pub(crate) inner: Container,
}

impl Set {
    pub fn new(set: HashSet<Value>) -> Self {
        Self {
            inner: Container::new(set.into_iter().map(|v| (v.clone(), v)).collect()),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::empty_with_db(db),
        }
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Ok(Self {
            inner: Container::from_db(root, db)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn contains(&self, value: &Value) -> Result<bool> {
        match self.inner.get(value.raw()) {
            Err(Error::Tree(e)) => {
                if e.is_key_not_found() {
                    Ok(false)
                } else {
                    Err(Error::Tree(e))
                }
            }
            Ok(_) => Ok(true),
            Err(e) => Err(e),
        }
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
                assert_eq!(key, value);
                Ok(value)
            }
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashSet<Value>> {
        self.iter().map(|v| v).collect()
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
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct Array {
    pub(crate) inner: Container,
}

impl Array {
    pub fn new(array: Vec<Value>) -> Self {
        Self {
            inner: Container::new(
                array
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| (Value::from(i as i64), v))
                    .collect(),
            ),
        }
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::empty_with_db(db),
        }
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Result<Self> {
        Ok(Self {
            inner: Container::from_db(root, db)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn get(&self, i: usize) -> Result<Value> {
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
                let index = i64::try_from(key.typed()).unwrap();
                Ok((index as usize, value))
            }
            Err(e) => Err(e),
        })
    }
    /// This is an expensive operation
    pub fn dump(&self) -> Result<HashMap<usize, Value>> {
        self.iter().map(|v| v).collect()
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
    fn test_dict() {
        let db = Box::new(MemDB::new());

        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0.insert(&Key::from("a"), &Value::from(1)).unwrap();
        dict0.insert(&Key::from("b"), &Value::from(2)).unwrap();
        dict0.update(&Key::from("a"), &Value::from(3)).unwrap();
        dict0.insert(&Key::from("c"), &Value::from(4)).unwrap();
        dict0.delete(&Key::from("c")).unwrap();
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

    #[test]
    fn test_set() {
        let db = Box::new(MemDB::new());

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

    #[test]
    fn test_array() {
        let db = Box::new(MemDB::new());

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

    #[test]
    fn test_nested() {
        let db = Box::new(MemDB::new());

        let mut nested = Dictionary::empty_with_db(db.clone());
        nested.insert(&Key::from("a"), &Value::from(1)).unwrap();
        nested.insert(&Key::from("b"), &Value::from(2)).unwrap();
        let nested_kvs0 = nested.dump().unwrap();

        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0.insert(&Key::from("x"), &Value::from(1)).unwrap();
        dict0
            .insert(&Key::from("y"), &Value::from(nested.clone()))
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

        match kvs1["y"].typed() {
            TypedValue::Dictionary(d) => {
                let nested_kvs1 = d.dump().unwrap();
                assert_eq!(nested_kvs0, nested_kvs1);
            }
            _ => unreachable!(),
        }
    }
}
