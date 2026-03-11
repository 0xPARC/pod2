//! This file implements the types defined at
//! <https://0xparc.github.io/pod2/values.html#dictionary-array-set> .

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    sync::{Arc, RwLock},
};

use anyhow::bail;
use dyn_clone::DynClone;
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

use super::serialization::{ordered_map, ordered_set};
#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{self, MerkleProof, MerkleTree};
use crate::{
    backends::plonky2::primitives::merkletree::MerkleTreeStateTransitionProof,
    middleware::{hash_str, Error, Hash, Key, RawValue, Result, Value, EMPTY_HASH, EMPTY_VALUE},
};

pub trait DB: Debug + DynClone + Sync + Send + merkletree::db::DB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Value>;
    fn store_value(&mut self, value: Value) -> anyhow::Result<()>;
}
dyn_clone::clone_trait_object!(DB);

/// MemDB implements the DB trait in a in-memory HashMap.
#[derive(Clone, Debug, Default)]
pub struct MemDB {
    nodes: Arc<RwLock<HashMap<RawValue, merkletree::Node>>>,
    values: Arc<RwLock<HashMap<RawValue, Value>>>,
}

impl MemDB {
    pub fn new() -> Self {
        Self::default()
    }
}

impl merkletree::db::DB for MemDB {
    fn load_node(&self, hash: RawValue) -> anyhow::Result<merkletree::Node> {
        let nodes = self.nodes.read().expect("lock not poisoned");

        if let Some(node) = nodes.get(&hash) {
            return Ok(node.clone());
        }

        if hash == EMPTY_VALUE {
            return Ok(merkletree::Node::Leaf(merkletree::Leaf::new(
                hash,
                EMPTY_VALUE,
            )));
        }

        bail!("MemDB: node not found: {}", hash);
    }

    fn store_node(&mut self, node: merkletree::Node) -> anyhow::Result<()> {
        let mut nodes = self.nodes.write().expect("lock not poisoned");
        nodes.insert(node.hash().into(), node);
        Ok(())
    }
}

impl DB for MemDB {
    fn load_value(&self, raw: RawValue) -> anyhow::Result<Value> {
        let values = self.values.read().expect("lock not poisoned");

        if let Some(value) = values.get(&raw) {
            return Ok(value.clone());
        } else {
            bail!("MemDB: value not found: {}", raw);
        }
    }
    fn store_value(&mut self, value: Value) -> anyhow::Result<()> {
        let mut values = self.values.write().expect("lock not poisoned");
        values.insert(value.raw(), value);
        Ok(())
    }
}

#[derive(Clone, Debug, JsonSchema)]
pub struct Container {
    mt: MerkleTree,
    db: Box<dyn DB>,
}

#[derive(Deserialize)]
struct ContainerAux {
    #[serde(serialize_with = "ordered_map")]
    kvs: HashMap<Value, Value>,
}

impl Serialize for Container {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let kvs: HashMap<Value, Value> = self.iter().collect()?;
        kvs.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Container {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Aux {
            #[serde(serialize_with = "ordered_map")]
            kvs: HashMap<Key, Value>,
        }
        let aux = Aux::deserialize(deserializer)?;
        Ok(Dictionary::new(aux.kvs))
    }
}

impl PartialEq for Container {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
    }
}
impl Eq for Container {}

impl Container {
    pub fn new(kvs: HashMap<Value, Value>) -> Self {
        let db = Box::new(MemDB::new());
        let mt = MerkleTree::empty_with_db(db.clone());
        let mut container = Self { mt, db };
        for (k, v) in kvs {
            container.insert(k, v).expect("no duplicates, no db errors");
        }
        container
    }
    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self::from_db(EMPTY_HASH, db)
    }
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Self {
        Self {
            mt: MerkleTree::from_db(root, db.clone()),
            db,
        }
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, key_raw: RawValue) -> Result<Value> {
        let value_raw = self.mt.get(&key_raw)?;
        let value = self.db.load_value(value_raw).expect("TODO");
        Ok(value)
    }
    pub fn prove(&self, key_raw: RawValue) -> Result<(Value, MerkleProof)> {
        let (value_raw, mtp) = self.mt.prove(&key_raw)?;
        let value = self.db.load_value(value_raw).expect("TODO");
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key_raw: RawValue) -> Result<MerkleProof> {
        Ok(self.mt.prove_nonexistence(&key_raw)?)
    }
    pub fn insert(&mut self, key: Value, value: Value) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.insert(&key.raw(), &value.raw())?;
        self.db.store_value(key).expect("TODO");
        self.db.store_value(value).expect("TODO");
        Ok(mtp)
    }
    pub fn update(
        &mut self,
        key_raw: RawValue,
        value: Value,
    ) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.update(&key_raw, &value.raw())?;
        self.db.store_value(value).unwrap();
        Ok(mtp)
    }
    pub fn delete(&mut self, key_raw: RawValue) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.delete(&key_raw)?;
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
    pub fn iter(&self) -> impl Iterator<Item = Result<(Value, Value)>> + use<'_> {
        self.mt.iter().map(|(key_raw, value_raw)| {
            let key = self.db.load_value(key_raw).expect("TODO");
            let value = self.db.load_value(value_raw).expect("TODO");
            Ok((key, value))
        })
    }
}

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Dictionary {
    inner: Container,
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
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::from_db(root, db),
        }
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
            Ok((key, value)) => Ok((String::try_from(key.typed()).expect("TODO"), value)),
            Err(e) => Err(e),
        })
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
pub struct Set {
    inner: Container,
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
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::from_db(root, db),
        }
    }
    pub fn commitment(&self) -> Hash {
        self.inner.commitment()
    }
    pub fn contains(&self, value: &Value) -> Result<bool> {
        // self.inner.get(value.raw())
        todo!()
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
}

impl PartialEq for Set {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}
impl Eq for Set {}

impl<'de> Deserialize<'de> for Set {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize, JsonSchema)]
        struct Aux {
            #[serde(serialize_with = "ordered_set")]
            set: HashSet<Value>,
        }
        let aux = Aux::deserialize(deserializer)?;
        Ok(Set::new(aux.set))
    }
}

/// Array: the elements are placed at the value field of each leaf, and the key field is just the
/// array index (integer).
///    leaf.key=i
///    leaf.value=original_value
/// Due to its construction this should be seen as a sparse array, where there can be gaps
/// (unused indices).
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Array {
    inner: Container,
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
    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Self {
        Self {
            inner: Container::from_db(root, db),
        }
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
}

impl PartialEq for Array {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}
impl Eq for Array {}

impl<'de> Deserialize<'de> for Array {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize, JsonSchema)]
        struct Aux {
            array: Vec<Value>,
        }
        let aux = Aux::deserialize(deserializer)?;
        Ok(Array::new(aux.array))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dict() {
        let db = Box::new(MemDB::new());

        let mut dict0 = Dictionary::empty_with_db(db.clone());
        dict0.insert(&Key::from("a"), &Value::from(1)).unwrap();
        dict0.insert(&Key::from("b"), &Value::from(2)).unwrap();
        dict0.update(&Key::from("a"), &Value::from(3)).unwrap();
        dict0.insert(&Key::from("c"), &Value::from(4)).unwrap();
        dict0.delete(&Key::from("c")).unwrap();
        let kvs0: HashMap<String, Value> = dict0.iter().map(|kv| kv.unwrap()).collect();
        assert_eq!(
            kvs0,
            [
                ("a".to_string(), Value::from(3)),
                ("b".to_string(), Value::from(2))
            ]
            .into_iter()
            .collect()
        );
        let dict1 = Dictionary::from_db(dict0.commitment(), db);
        let kvs1: HashMap<String, Value> = dict1.iter().map(|kv| kv.unwrap()).collect();
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

        let s0: HashSet<Value> = set0.iter().map(|v| v.unwrap()).collect();
        assert_eq!(s0, [Value::from(1), Value::from(3)].into_iter().collect());
        let set1 = Set::from_db(set0.commitment(), db);
        let s1: HashSet<Value> = set1.iter().map(|v| v.unwrap()).collect();
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

        let a0: HashMap<usize, Value> = arr0.iter().map(|kv| kv.unwrap()).collect();
        assert_eq!(
            a0,
            [(0, Value::from("a")), (2, Value::from("c"))]
                .into_iter()
                .collect()
        );
        let arr1 = Array::from_db(arr0.commitment(), db);
        let a1: HashMap<usize, Value> = arr1.iter().map(|kv| kv.unwrap()).collect();
        assert_eq!(a0, a1);
    }
}
