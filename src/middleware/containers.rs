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
    max_depth: usize,
    #[serde(serialize_with = "ordered_map")]
    kvs: HashMap<Key, Value>,
}

#[macro_export]
macro_rules! dict {
    ($max_depth:expr, { $($key:expr => $val:expr),* , }) => (
        $crate::dict!($max_depth, { $($key => $val),* })
    );
    ($max_depth:expr, { $($key:expr => $val:expr),* }) => ({
        let mut map = ::std::collections::HashMap::new();
        $( map.insert($crate::middleware::Key::from($key), $crate::middleware::Value::from($val)); )*
        $crate::middleware::containers::Dictionary::new($max_depth, map)
    });
}

impl Dictionary {
    /// max_depth determines the depth of the underlying MerkleTree, allowing to
    /// store 2^max_depth elements in the Dictionary
    pub fn new(max_depth: usize, kvs: HashMap<Key, Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> =
            kvs.iter().map(|(k, v)| (k.raw(), v.raw())).collect();
        Ok(Self {
            mt: MerkleTree::new(max_depth, &kvs_raw)?,
            max_depth,
            kvs,
        })
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
    pub fn verify(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &Key,
        value: &Value,
    ) -> Result<()> {
        let key = key.raw();
        Ok(MerkleTree::verify(
            max_depth,
            root,
            proof,
            &key,
            &value.raw(),
        )?)
    }
    pub fn verify_nonexistence(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &Key,
    ) -> Result<()> {
        let key = key.raw();
        Ok(MerkleTree::verify_nonexistence(
            max_depth, root, proof, &key,
        )?)
    }
    pub fn verify_state_transition(
        max_depth: usize,
        proof: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        MerkleTree::verify_state_transition(max_depth, proof).map_err(|e| e.into())
    }
    // TODO: Rename to dict to be consistent maybe?
    pub fn kvs(&self) -> &HashMap<Key, Value> {
        &self.kvs
    }
    pub fn max_depth(&self) -> usize {
        self.max_depth
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
            max_depth: usize,
        }
        let aux = Aux::deserialize(deserializer)?;
        Dictionary::new(aux.max_depth, aux.kvs).map_err(serde::de::Error::custom)
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
    max_depth: usize,
    #[serde(serialize_with = "ordered_set")]
    set: HashSet<Value>,
}

impl Set {
    /// max_depth determines the depth of the underlying MerkleTree, allowing to
    /// store 2^max_depth elements in the Array
    pub fn new(max_depth: usize, set: HashSet<Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = set
            .iter()
            .map(|e| {
                let rv = e.raw();
                (rv, rv)
            })
            .collect();
        Ok(Self {
            mt: MerkleTree::new(max_depth, &kvs_raw)?,
            max_depth,
            set,
        })
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
    pub fn verify(max_depth: usize, root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let rv = value.raw();
        Ok(MerkleTree::verify(max_depth, root, proof, &rv, &rv)?)
    }
    pub fn verify_nonexistence(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        value: &Value,
    ) -> Result<()> {
        let rv = value.raw();
        Ok(MerkleTree::verify_nonexistence(
            max_depth, root, proof, &rv,
        )?)
    }
    pub fn verify_state_transition(
        max_depth: usize,
        proof: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        MerkleTree::verify_state_transition(max_depth, proof).map_err(|e| e.into())
    }
    pub fn set(&self) -> &HashSet<Value> {
        &self.set
    }
    pub fn max_depth(&self) -> usize {
        self.max_depth
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
            max_depth: usize,
        }
        let aux = Aux::deserialize(deserializer)?;
        Set::new(aux.max_depth, aux.set).map_err(serde::de::Error::custom)
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
    max_depth: usize,
    array: Vec<Value>,
}

impl Array {
    /// max_depth determines the depth of the underlying MerkleTree, allowing to
    /// store 2^max_depth elements in the Array
    pub fn new(max_depth: usize, array: Vec<Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = array
            .iter()
            .enumerate()
            .map(|(i, e)| (RawValue::from(i as i64), e.raw()))
            .collect();

        Ok(Self {
            mt: MerkleTree::new(max_depth, &kvs_raw)?,
            max_depth,
            array,
        })
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
    pub fn verify(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        i: usize,
        value: &Value,
    ) -> Result<()> {
        Ok(MerkleTree::verify(
            max_depth,
            root,
            proof,
            &RawValue::from(i as i64),
            &value.raw(),
        )?)
    }
    pub fn verify_state_transition(
        max_depth: usize,
        proof: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        MerkleTree::verify_state_transition(max_depth, proof).map_err(|e| e.into())
    }
    pub fn array(&self) -> &[Value] {
        &self.array
    }
    pub fn max_depth(&self) -> usize {
        self.max_depth
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
            max_depth: usize,
        }
        let aux = Aux::deserialize(deserializer)?;
        Array::new(aux.max_depth, aux.array).map_err(serde::de::Error::custom)
    }
}
