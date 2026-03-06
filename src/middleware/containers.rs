//! This file implements the types defined at
//! <https://0xparc.github.io/pod2/values.html#dictionary-array-set> .

use std::collections::{HashMap, HashSet};

use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

use super::serialization::{ordered_map, ordered_set};
#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::{
    backends::plonky2::primitives::merkletree::MerkleTreeStateTransitionProof,
    middleware::{Error, Hash, Key, RawValue, Result, Value},
};

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Dictionary {
    #[serde(skip)]
    #[schemars(skip)]
    mt: MerkleTree,
    #[serde(serialize_with = "ordered_map")]
    kvs: HashMap<Key, Value>,
}

#[macro_export]
macro_rules! dict {
    ({ $($key:expr => $val:expr),* , }) => (
        $crate::dict!({ $($key => $val),* })
    );
    ({ $($key:expr => $val:expr),* }) => ({
        let mut map = ::std::collections::HashMap::new();
        $( map.insert($crate::middleware::Key::from($key), $crate::middleware::Value::from($val)); )*
        $crate::middleware::containers::Dictionary::new( map)
    });
}

impl Dictionary {
    pub fn new(kvs: HashMap<Key, Value>) -> Self {
        let kvs_raw: HashMap<RawValue, RawValue> =
            kvs.iter().map(|(k, v)| (k.raw(), v.raw())).collect();
        Self {
            mt: MerkleTree::new(&kvs_raw),
            kvs,
        }
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, key: &Key) -> Result<&Value> {
        self.kvs
            .get(key)
            .ok_or_else(|| Error::custom(format!("key \"{}\" not found", key.name())))
    }
    pub fn prove(&self, key: &Key) -> Result<(&Value, MerkleProof)> {
        let (_, mtp) = self.mt.prove(&key.raw())?;
        let value = self.kvs.get(key).expect("key exists");
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key: &Key) -> Result<MerkleProof> {
        Ok(self.mt.prove_nonexistence(&key.raw())?)
    }
    pub fn insert(&mut self, key: &Key, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.insert(&key.raw(), &value.raw())?;
        self.kvs.insert(key.clone(), value.clone());
        Ok(mtp)
    }
    pub fn update(&mut self, key: &Key, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.update(&key.raw(), &value.raw())?;
        self.kvs.insert(key.clone(), value.clone());
        Ok(mtp)
    }
    pub fn delete(&mut self, key: &Key) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.delete(&key.raw())?;
        self.kvs.remove(key);
        Ok(mtp)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &Key, value: &Value) -> Result<()> {
        let key = key.raw();
        Ok(MerkleTree::verify(root, proof, &key, &value.raw())?)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &Key) -> Result<()> {
        let key = key.raw();
        Ok(MerkleTree::verify_nonexistence(root, proof, &key)?)
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        MerkleTree::verify_state_transition(proof).map_err(|e| e.into())
    }
    // TODO: Rename to dict to be consistent maybe?
    pub fn kvs(&self) -> &HashMap<Key, Value> {
        &self.kvs
    }
}

impl PartialEq for Dictionary {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
    }
}
impl Eq for Dictionary {}

impl<'de> Deserialize<'de> for Dictionary {
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

/// Set: the value field of the leaf is unused, and the key contains the hash of the element.
///    leaf.key=hash(original_value)
///    leaf.value=0
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Set {
    #[serde(skip)]
    #[schemars(skip)]
    mt: MerkleTree,
    #[serde(serialize_with = "ordered_set")]
    set: HashSet<Value>,
}

impl Set {
    pub fn new(set: HashSet<Value>) -> Self {
        let kvs_raw: HashMap<RawValue, RawValue> = set
            .iter()
            .map(|e| {
                let rv = e.raw();
                (rv, rv)
            })
            .collect();
        Self {
            mt: MerkleTree::new(&kvs_raw),
            set,
        }
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn contains(&self, value: &Value) -> bool {
        self.set.contains(value)
    }
    pub fn prove(&self, value: &Value) -> Result<MerkleProof> {
        let rv = value.raw();
        let (_, proof) = self.mt.prove(&rv)?;
        Ok(proof)
    }
    pub fn prove_nonexistence(&self, value: &Value) -> Result<MerkleProof> {
        let rv = value.raw();
        Ok(self.mt.prove_nonexistence(&rv)?)
    }
    pub fn insert(&mut self, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let raw_value = value.raw();
        let mtp = self.mt.insert(&raw_value, &raw_value)?;
        self.set.insert(value.clone());
        Ok(mtp)
    }
    pub fn delete(&mut self, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.delete(&value.raw())?;
        self.set.remove(value);
        Ok(mtp)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let rv = value.raw();
        Ok(MerkleTree::verify(root, proof, &rv, &rv)?)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let rv = value.raw();
        Ok(MerkleTree::verify_nonexistence(root, proof, &rv)?)
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        MerkleTree::verify_state_transition(proof).map_err(|e| e.into())
    }
    pub fn set(&self) -> &HashSet<Value> {
        &self.set
    }
}

impl PartialEq for Set {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
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
#[derive(Clone, Debug, Serialize, JsonSchema)]
pub struct Array {
    #[serde(skip)]
    #[schemars(skip)]
    mt: MerkleTree,
    array: Vec<Value>,
}

impl Array {
    pub fn new(array: Vec<Value>) -> Self {
        let kvs_raw: HashMap<RawValue, RawValue> = array
            .iter()
            .enumerate()
            .map(|(i, e)| (RawValue::from(i as i64), e.raw()))
            .collect();

        Self {
            mt: MerkleTree::new(&kvs_raw),
            array,
        }
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, i: usize) -> Result<&Value> {
        self.array.get(i).ok_or_else(|| {
            Error::custom(format!("index {} out of bounds 0..{}", i, self.array.len()))
        })
    }
    pub fn prove(&self, i: usize) -> Result<(&Value, MerkleProof)> {
        let (_, mtp) = self.mt.prove(&RawValue::from(i as i64))?;
        let value = self.array.get(i).expect("valid index");
        Ok((value, mtp))
    }
    pub fn update(&mut self, i: usize, value: &Value) -> Result<MerkleTreeStateTransitionProof> {
        let mtp = self.mt.update(&(i as i64).into(), &value.raw())?;
        self.array[i] = value.clone();
        Ok(mtp)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, i: usize, value: &Value) -> Result<()> {
        Ok(MerkleTree::verify(
            root,
            proof,
            &RawValue::from(i as i64),
            &value.raw(),
        )?)
    }
    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> Result<()> {
        MerkleTree::verify_state_transition(proof).map_err(|e| e.into())
    }
    pub fn array(&self) -> &[Value] {
        &self.array
    }
}

impl PartialEq for Array {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
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
