/// This file implements the types defined at
/// https://0xparc.github.io/pod2/values.html#dictionary-array-set .
use anyhow::Result;
use std::collections::HashMap;

use crate::constants::MAX_DEPTH;

#[cfg(feature = "backend_plonky2")]
use crate::backends::plonky2::primitives::merkletree::{Iter as TreeIter, MerkleProof, MerkleTree};

use super::basetypes::{hash_value, Hash, Value, EMPTY};

/// Dictionary: the user original keys and values are hashed to be used in the leaf.
///    leaf.key=hash(original_key)
///    leaf.value=hash(original_value)
#[derive(Clone, Debug)]
pub struct Dictionary {
    // exposed with pub(crate) so that it can be modified at tests
    pub(crate) mt: MerkleTree,
}

impl Dictionary {
    pub fn new(kvs: &HashMap<Hash, Value>) -> Result<Self> {
        let kvs: HashMap<Value, Value> = kvs.iter().map(|(&k, &v)| (Value(k.0), v)).collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, key: &Value) -> Result<Value> {
        self.mt.get(key)
    }
    pub fn prove(&self, key: &Value) -> Result<(Value, MerkleProof)> {
        self.mt.prove(key)
    }
    pub fn prove_nonexistence(&self, key: &Value) -> Result<MerkleProof> {
        self.mt.prove_nonexistence(key)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, key: &Value, value: &Value) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, key, value)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &Value) -> Result<()> {
        MerkleTree::verify_nonexistence(MAX_DEPTH, root, proof, key)
    }
    pub fn iter(&self) -> TreeIter {
        self.mt.iter()
    }
}
impl<'a> IntoIterator for &'a Dictionary {
    type Item = (&'a Value, &'a Value);
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
    pub fn new(set: &Vec<Value>) -> Result<Self> {
        let kvs: HashMap<Value, Value> = set
            .iter()
            .map(|e| {
                let h = hash_value(e);
                (Value::from(h), EMPTY)
            })
            .collect();
        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn contains(&self, value: &Value) -> Result<bool> {
        self.mt.contains(value)
    }
    pub fn prove(&self, value: &Value) -> Result<MerkleProof> {
        let (_, proof) = self.mt.prove(value)?;
        Ok(proof)
    }
    pub fn prove_nonexistence(&self, value: &Value) -> Result<MerkleProof> {
        self.mt.prove_nonexistence(value)
    }
    pub fn verify(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, value, &EMPTY)
    }
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, value: &Value) -> Result<()> {
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
    pub fn new(array: &Vec<Value>) -> Result<Self> {
        let kvs: HashMap<Value, Value> = array
            .iter()
            .enumerate()
            .map(|(i, &e)| (Value::from(i as i64), e))
            .collect();

        Ok(Self {
            mt: MerkleTree::new(MAX_DEPTH, &kvs)?,
        })
    }
    pub fn commitment(&self) -> Hash {
        self.mt.root()
    }
    pub fn get(&self, i: usize) -> Result<Value> {
        self.mt.get(&Value::from(i as i64))
    }
    pub fn prove(&self, i: usize) -> Result<(Value, MerkleProof)> {
        self.mt.prove(&Value::from(i as i64))
    }
    pub fn verify(root: Hash, proof: &MerkleProof, i: usize, value: &Value) -> Result<()> {
        MerkleTree::verify(MAX_DEPTH, root, proof, &Value::from(i as i64), value)
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

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_dictionary() -> Result<()> {
        // prepare key-value entries
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(hash_value(&Value::from(i)), Value::from(1000 + i));
        }

        let dict = Dictionary::new(&kvs)?;

        // get the leafs into a hashmap
        let leafs: HashMap<Value, Value> = dict.iter().map(|(&k, &v)| (k, v)).collect();

        // check that the leafs `keys` appear in the original kvs and they have
        // the same `value`
        for (k, v) in leafs.clone() {
            assert_eq!(v, *leafs.get(&k).unwrap());
        }

        // reconstruct the tree from the leafs
        let tree2 = MerkleTree::new(32, &leafs)?;

        // check that the new tree has the same root as the original dict
        assert_eq!(dict.commitment(), tree2.root());

        Ok(())
    }

    #[test]
    fn test_set() -> Result<()> {
        // prepare set elements
        let mut set_elems: Vec<Value> = Vec::new();
        for i in 0..8 {
            set_elems.push(Value::from(i));
        }

        let set = Set::new(&set_elems)?;

        // get the leafs into a hashmap
        let leafs: HashMap<Value, Value> = set.iter().map(|(&k, &v)| (k, v)).collect();

        // check that the leafs `keys` appear in the original kvs and they have
        // the same `value`
        for (k, v) in leafs.clone() {
            assert_eq!(v, *leafs.get(&k).unwrap());
        }

        // reconstruct the tree from the leafs
        let tree2 = MerkleTree::new(32, &leafs)?;

        // check that the new tree has the same root as the original set
        assert_eq!(set.commitment(), tree2.root());

        Ok(())
    }

    #[test]
    fn test_array() -> Result<()> {
        // prepare set elements
        let mut array_elems: Vec<Value> = Vec::new();
        for i in 0..8 {
            array_elems.push(Value::from(i));
        }

        let array = Array::new(&array_elems)?;

        // get the leafs into a hashmap
        let leafs: HashMap<Value, Value> = array.iter().map(|(&k, &v)| (k, v)).collect();

        // check that the leafs `keys` appear in the original kvs and they have
        // the same `value`
        for (k, v) in leafs.clone() {
            assert_eq!(v, *leafs.get(&k).unwrap());
        }

        // reconstruct the tree from the leafs
        let tree2 = MerkleTree::new(32, &leafs)?;

        // check that the new tree has the same root as the original array
        assert_eq!(array.commitment(), tree2.root());

        Ok(())
    }
}
