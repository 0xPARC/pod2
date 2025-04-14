use std::collections::{HashMap, HashSet};

/// This file implements the types defined at
/// https://0xparc.github.io/pod2/values.html#dictionary-array-set .
use anyhow::{anyhow, Result};

#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{MerkleProof, MerkleTree};
use crate::{
    constants::MAX_DEPTH,
    middleware::{hash_value, Hash, Key, RawValue, Value, EMPTY_VALUE},
};

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug)]
pub struct Dictionary {
    mt: MerkleTree,
    kvs: HashMap<Key, Value>,
}

impl Dictionary {
    pub fn new(kvs: HashMap<Key, Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = kvs
            .iter()
            .map(|(k, v)| (RawValue(k.hash().0), v.raw()))
            .collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs_raw)?,
            kvs,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, key: &Key) -> Result<&Value> {
        self.kvs
            .get(key)
            .ok_or_else(|| anyhow!("key \"{}\" not found", key.name()))
    }
    pub fn prove(&self, key: &Key) -> Result<(&Value, MerkleProof)> {
        let (_, mtp) = self.mt.prove(&RawValue(key.hash().0))?;
        let value = self.kvs.get(key).expect("key exists");
        Ok((value, mtp))
    }
    pub fn prove_nonexistence(&self, key: &Key) -> Result<MerkleProof> {
        self.mt.prove_nonexistence(&RawValue(key.hash().0))
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &Key, value: &Value) -> Result<()> {
        let key = RawValue(key.hash().0);
        MerkleTree::verify(MAX_DEPTH, root, proof, &key, &value.raw())
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &Key) -> Result<()> {
        let key = RawValue(key.hash().0);
        MerkleTree::verify_nonexistence(MAX_DEPTH, root, proof, &key)
    }
    // TODO: Rename to dict to be consistent maybe?
    pub fn kvs(&self) -> &HashMap<Key, Value> {
        &self.kvs
    }
}
// impl<'a> IntoIterator for &'a Dictionary {
//     type Item = (&'a RawValue, &'a RawValue);
//     type IntoIter = TreeIter<'a>;
//
//     fn into_iter(self) -> Self::IntoIter {
//         self.mt.iter()
//     }
// }

impl PartialEq for Dictionary {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
    }
}
impl Eq for Dictionary {}

/// Set: the value field of the leaf is unused, and the key contains the hash of the element.
///    leaf.key=hash(original_value)
///    leaf.value=0
#[derive(Clone, Debug)]
pub struct Set {
    mt: MerkleTree,
    set: HashSet<Value>,
}

impl Set {
    pub fn new(set: HashSet<Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = set
            .iter()
            .map(|e| {
                let h = hash_value(&e.raw());
                (RawValue::from(h), EMPTY_VALUE)
            })
            .collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs_raw)?,
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
        self.mt.prove_nonexistence(&RawValue::from(h))
    }
    pub fn verify(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let h = hash_value(&value.raw());
        MerkleTree::verify(MAX_DEPTH, root, proof, &RawValue::from(h), &EMPTY_VALUE)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        let h = hash_value(&value.raw());
        MerkleTree::verify_nonexistence(MAX_DEPTH, root, proof, &RawValue::from(h))
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

/// Array: the elements are placed at the value field of each leaf, and the key field is just the
/// array index (integer).
///    leaf.key=i
///    leaf.value=original_value
#[derive(Clone, Debug)]
pub struct Array {
    mt: MerkleTree,
    array: Vec<Value>,
}

impl Array {
    pub fn new(array: Vec<Value>) -> Result<Self> {
        let kvs_raw: HashMap<RawValue, RawValue> = array
            .iter()
            .enumerate()
            .map(|(i, e)| (RawValue::from(i as i64), e.raw()))
            .collect();

        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs_raw)?,
            array,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, i: usize) -> Result<&Value> {
        self.array
            .get(i)
            .ok_or_else(|| anyhow!("index {} out of bounds 0..{}", i, self.array.len()))
    }
    pub fn prove(&self, i: usize) -> Result<(&Value, MerkleProof)> {
        let (_, mtp) = self.mt.prove(&RawValue::from(i as i64))?;
        let value = self.array.get(i).expect("valid index");
        Ok((value, mtp))
    }
    pub fn verify(root: Hash, proof: &MerkleProof, i: usize, value: &Value) -> Result<()> {
        MerkleTree::verify(
            MAX_DEPTH,
            root,
            proof,
            &RawValue::from(i as i64),
            &value.raw(),
        )
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
