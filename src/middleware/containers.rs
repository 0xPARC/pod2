use std::collections::HashMap;

/// This file implements the types defined at
/// https://0xparc.github.io/pod2/values.html#dictionary-array-set .
use anyhow::Result;

#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{Iter as TreeIter, MerkleProof, MerkleTree};
use crate::{
    constants::MAX_DEPTH,
    middleware::basetypes::{hash_value, Hash, RawValue, EMPTY_VALUE},
};

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug)]
pub struct Dictionary {
    // exposed with pub(crate) so that it can be modified at tests
    pub(crate) mt: MerkleTree,
}

impl Dictionary {
    pub fn new(kvs: &HashMap<Hash, RawValue>) -> Result<Self> {
        let kvs: HashMap<RawValue, RawValue> =
            kvs.iter().map(|(&k, &v)| (RawValue(k.0), v)).collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, key: &RawValue) -> Result<RawValue> {
        self.mt.get(key)
    }
    pub fn prove(&self, key: &RawValue) -> Result<(RawValue, MerkleProof)> {
        self.mt.prove(key)
    }
    pub fn prove_nonexistence(&self, key: &RawValue) -> Result<MerkleProof> {
        self.mt.prove_nonexistence(key)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &RawValue, value: &RawValue) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, key, value)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &RawValue) -> Result<()> {
        MerkleTree::verify_nonexistence(MAX_DEPTH, root, proof, key)
    }
    pub fn iter(&self) -> TreeIter {
        self.mt.iter()
    }
}
impl<'a> IntoIterator for &'a Dictionary {
    type Item = (&'a RawValue, &'a RawValue);
    type IntoIter = TreeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.mt.iter()
    }
}

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
}

impl Set {
    pub fn new(set: &[RawValue]) -> Result<Self> {
        let kvs: HashMap<RawValue, RawValue> = set
            .iter()
            .map(|e| {
                let h = hash_value(e);
                (RawValue::from(h), EMPTY_VALUE)
            })
            .collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn contains(&self, value: &RawValue) -> Result<bool> {
        self.mt.contains(value)
    }
    pub fn prove(&self, value: &RawValue) -> Result<MerkleProof> {
        let (_, proof) = self.mt.prove(value)?;
        Ok(proof)
    }
    pub fn prove_nonexistence(&self, value: &RawValue) -> Result<MerkleProof> {
        self.mt.prove_nonexistence(value)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, value: &RawValue) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, value, &EMPTY_VALUE)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, value: &RawValue) -> Result<()> {
        MerkleTree::verify_nonexistence(MAX_DEPTH, root, proof, value)
    }
    pub fn iter(&self) -> TreeIter {
        self.mt.iter()
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
}

impl Array {
    pub fn new(array: &[RawValue]) -> Result<Self> {
        let kvs: HashMap<RawValue, RawValue> = array
            .iter()
            .enumerate()
            .map(|(i, &e)| (RawValue::from(i as i64), e))
            .collect();

        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, i: usize) -> Result<RawValue> {
        self.mt.get(&RawValue::from(i as i64))
    }
    pub fn prove(&self, i: usize) -> Result<(RawValue, MerkleProof)> {
        self.mt.prove(&RawValue::from(i as i64))
    }
    pub fn verify(root: Hash, proof: &MerkleProof, i: usize, value: &RawValue) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, &RawValue::from(i as i64), value)
    }
    pub fn iter(&self) -> TreeIter {
        self.mt.iter()
    }
}

impl PartialEq for Array {
    fn eq(&self, other: &Self) -> bool {
        self.mt.root() == other.mt.root()
    }
}
impl Eq for Array {}
