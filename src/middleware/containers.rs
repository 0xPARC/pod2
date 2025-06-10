//! This file implements the types defined at
//! https://0xparc.github.io/pod2/values.html#dictionary-array-set .

use std::collections::{HashMap, HashSet};

use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize};

use super::serialization::{ordered_map, ordered_set};
#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::middleware::{hash_value, Error, Hash, Key, RawValue, Result, Value};

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

impl Dictionary {
    /// max_depth determines the depth of the underlying MerkleTree, allowing to
    /// store 2^max_depth elements in the Dictionary
    pub fn new(max_depth: usize, kvs: HashMap<Key, Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = kvs
            .iter()
            .map(|(k, v)| (RawValue(k.hash().0), v.raw()))
            .collect();
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
        let (_, mtp) = self.mt.prove(&RawValue(key.hash().0))?;
        let value = self.kvs.get(key).expect("key exists");
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key: &Key) -> Result<MerkleProof> {
        Ok(self.mt.prove_nonexistence(&RawValue(key.hash().0))?)
    }
    pub fn verify(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &Key,
        value: &Value,
    ) -> Result<()> {
        let key = RawValue(key.hash().0);
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
        let key = RawValue(key.hash().0);
        Ok(MerkleTree::verify_nonexistence(
            max_depth, root, proof, &key,
        )?)
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
                let h = hash_value(&e.raw());
                (RawValue::from(h), RawValue::from(h))
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
        let h = hash_value(&value.raw());
        let (_, proof) = self.mt.prove(&RawValue::from(h))?;
        Ok(proof)
    }
    pub fn prove_nonexistence(&self, value: &Value) -> Result<MerkleProof> {
        let h = hash_value(&value.raw());
        Ok(self.mt.prove_nonexistence(&RawValue::from(h))?)
    }
    pub fn verify(max_depth: usize, root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let h = hash_value(&value.raw());
        Ok(MerkleTree::verify(
            max_depth,
            root,
            proof,
            &RawValue::from(h),
            &RawValue::from(h),
        )?)
    }
    pub fn verify_nonexistence(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        value: &Value,
    ) -> Result<()> {
        let h = hash_value(&value.raw());
        Ok(MerkleTree::verify_nonexistence(
            max_depth,
            root,
            proof,
            &RawValue::from(h),
        )?)
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
            max_depth: usize,
        }
        let aux = Aux::deserialize(deserializer)?;
        Array::new(aux.max_depth, aux.array).map_err(serde::de::Error::custom)
    }
}
