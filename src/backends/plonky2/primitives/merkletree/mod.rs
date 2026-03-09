//! Module that implements the MerkleTree specified at
//! <https://0xparc.github.io/pod2/merkletree.html> .
use std::{collections::HashMap, fmt, iter::IntoIterator};

use anyhow::{anyhow, Result};
use itertools::zip_eq;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::NUM_HASH_OUT_ELTS, hashing::PlonkyPermutation, poseidon::PoseidonPermutation,
    },
};
use serde::{Deserialize, Serialize};

use crate::middleware::{Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F};

pub mod circuit;
pub use circuit::*;
mod db;
use db::DB;
pub mod error;
pub use error::{TreeError, TreeResult};

/// Theoretical max depth of a merkle tree.  This limits appears because we store keys of 256 bits.
const MAX_DEPTH: usize = 256;

/// Implements the MerkleTree specified at
/// <https://0xparc.github.io/pod2/merkletree.html>
#[derive(Clone, Debug)]
pub struct MerkleTree {
    root: Hash,
    db: Box<dyn DB>,
}

impl PartialEq for MerkleTree {
    fn eq(&self, other: &Self) -> bool {
        self.root() == other.root()
    }
}
impl Eq for MerkleTree {}

impl MerkleTree {
    /// builds a new `MerkleTree` where the leaves contain the given key-values
    // NOTE: this method is kept for legacy compatibility at higher levels of the pod2 repo. It
    // should be replaced by the `new_with_b` or `from_db` or `empty_with_db` or similar, and the
    // `.unwrap()` occurrences should be removed.
    pub fn new(kvs: &HashMap<RawValue, RawValue>) -> Self {
        let db = db::MemDB::new();
        Self::new_with_db(Box::new(db), kvs)
    }
    pub fn new_with_db(db: Box<dyn DB>, kvs: &HashMap<RawValue, RawValue>) -> Self {
        // Start with an empty node as root.
        let (root, db) = {
            let mut db = db;

            // Iterate over key-value pairs (if any) and add them.
            let mut root = EMPTY_HASH;
            db.store_node(Node::Leaf(Leaf::new(root.into(), EMPTY_VALUE)))
                .unwrap();
            for (k, v) in kvs.iter() {
                root =
                    Self::apply_op(db.as_mut(), MerkleTreeOp::Insert, root, *k, Some(*v)).unwrap();
            }
            (root, db)
        };

        // Fill in hashes.
        Self { root, db }
    }

    pub fn empty_with_db(db: Box<dyn DB>) -> Self {
        Self::from_db(EMPTY_HASH, db)
    }

    pub fn from_db(root: Hash, db: Box<dyn DB>) -> Self {
        Self { root, db }
    }

    /// returns the root of the tree
    pub fn root(&self) -> Hash {
        self.root
    }

    /// Goes down from the current node until it encounters a terminal node,
    /// viz. a leaf or empty node, or until it reaches the maximum depth. The
    /// `siblings` parameter is used to store the siblings while going down to
    /// the leaf, if the given parameter is set to `None`, then no siblings are
    /// stored. In this way, the same method `down` can be used by MerkleTree
    /// methods `get`, `contains`, `prove` and `prove_nonexistence`.
    ///
    /// Be aware that this method will return the found leaf at the given path,
    /// which may contain a different key and value than the expected one. And
    /// while it does not return explicitly a `siblings` variable, the input
    /// `siblings` is modified adding there the siblings found along the path.
    fn down(
        db: &dyn DB,
        path_and_lvl: (Vec<bool>, usize), // path and lvl
        curr_node_hash: Hash,             // hash of current level node
        new_key: RawValue,                // key to be added/found at the leaf
        mut siblings: Option<&mut Vec<Hash>>,
        op: MerkleTreeOp,
    ) -> TreeResult<Option<(RawValue, RawValue)>> {
        let (path, lvl) = path_and_lvl;

        if lvl > MAX_DEPTH {
            return Err(TreeError::max_depth());
        }

        if curr_node_hash == EMPTY_HASH {
            return Ok(None);
        }

        let node = db.load_node(curr_node_hash.into())?;
        match node {
            Node::Intermediate(n) => {
                if path[lvl] {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.left);
                    }
                    Self::down(db, (path, lvl + 1), n.right, new_key, siblings, op)
                } else {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.right);
                    }
                    Self::down(db, (path, lvl + 1), n.left, new_key, siblings, op)
                }
            }
            Node::Leaf(old_leaf) => {
                if op == MerkleTreeOp::ReadOnly {
                    return Ok(Some((old_leaf.key, old_leaf.value)));
                }

                if new_key == old_leaf.key {
                    if op == MerkleTreeOp::Insert {
                        // in Insert, key should not exist
                        return Err(TreeError::key_exists());
                    }
                    // we're at the operation Update/Delete case
                    return Ok(Some((old_leaf.key, old_leaf.value)));
                }

                Self::down_till_divergence(
                    lvl,
                    curr_node_hash.into(),
                    old_leaf.path,
                    path,
                    siblings.ok_or(anyhow!("expected siblings, got None"))?,
                )?;
                Ok(Some((old_leaf.key, old_leaf.value)))
            }
        }
    }

    /// goes down through a 'virtual' path till finding a divergence. This
    /// method is used for when adding a new leaf another already existing leaf
    /// is found, so that both leaves (new and old) are pushed down the path
    /// till their keys diverge.
    fn down_till_divergence(
        lvl: usize,
        old_key: RawValue,
        old_path: Vec<bool>,
        new_path: Vec<bool>,
        siblings: &mut Vec<Hash>,
    ) -> TreeResult<()> {
        if lvl > MAX_DEPTH {
            return Err(TreeError::max_depth());
        }
        if old_path[lvl] == new_path[lvl] {
            siblings.push(EMPTY_HASH);
            return Self::down_till_divergence(lvl + 1, old_key, old_path, new_path, siblings);
        }
        // reached the divergence
        siblings.push(old_key.into());
        Ok(())
    }

    /// go up recursively updating the intermediate nodes
    fn up(
        db: &mut dyn DB,
        path: Vec<bool>,
        curr_lvl: usize,
        key: Hash,
        siblings: Vec<Hash>,
        op: MerkleTreeOp,
        // first_zeroes should be set to `true` when calling `up` from outside
        // the method itself. It is used internally to know when to go up
        // 'virtually' for the first batch of zeroes.
        first_zeroes: bool,
    ) -> Result<Hash> {
        // recall, in the delete case, the `key` is the `remaining_key`
        let key_node = db.load_node(key.into())?;
        if op == MerkleTreeOp::Delete
            && first_zeroes
            && matches!(key_node, Node::Leaf(..))
            && siblings[curr_lvl] == EMPTY_HASH
        {
            // - if we're at operation delete, the node that we're holding is a leaf,
            // and we're at the first consecutive zero siblings
            // - in operation Delete, go up till the first non-zero sibling and
            // pair the given key with that sibling.
            // This is only done for the first batch of zero siblings, that is,
            // after a non-zero sibling, no matter how many zero siblings it
            // has, don't do this logic anymore.
            if curr_lvl == 0 {
                return Ok(key);
            }
            return Self::up(db, path, curr_lvl - 1, key, siblings, op, true);
        }

        let node = if path[curr_lvl] {
            Intermediate::new(siblings[curr_lvl], key)
        } else {
            Intermediate::new(key, siblings[curr_lvl])
        };
        let node_hash = node.hash; // variable to avoid cloning `node` later

        // store in db
        db.store_node(Node::Intermediate(node))?;

        if curr_lvl == 0 {
            return Ok(node_hash);
        }
        Self::up(db, path, curr_lvl - 1, node_hash, siblings, op, false)
    }

    /// returns the value at the given key
    pub fn get(&self, key: &RawValue) -> TreeResult<RawValue> {
        let path = keypath(*key);
        let key_resolution = Self::down(
            self.db.as_ref(),
            (path, 0),
            self.root,
            *key,
            None,
            MerkleTreeOp::ReadOnly,
        )?;
        match key_resolution {
            Some((k, v)) if &k == key => Ok(v),
            _ => Err(TreeError::key_not_found()),
        }
    }

    /// returns a boolean indicating whether the key exists in the tree
    pub fn contains(&self, key: &RawValue) -> TreeResult<bool> {
        let path = keypath(*key);
        match Self::down(
            self.db.as_ref(),
            (path, 0),
            self.root,
            *key,
            None,
            MerkleTreeOp::ReadOnly,
        )? {
            Some((k, _)) if &k == key => Ok(true),
            _ => Ok(false),
        }
    }

    pub fn insert(
        &mut self,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<MerkleTreeStateTransitionProof> {
        let proof_non_existence = self.prove_nonexistence(key)?;

        let old_root: Hash = self.root;

        self.root = Self::apply_op(
            self.db.as_mut(),
            MerkleTreeOp::Insert,
            self.root,
            *key,
            Some(*value),
        )?;

        let (v, proof) = self.prove(key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Insert, // insertion
            old_root,
            op_proof: proof_non_existence,
            new_root: self.root,
            op_key: *key,
            op_value: *value,
            value: None,
            siblings: proof.siblings,
        })
    }

    pub fn update(
        &mut self,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<MerkleTreeStateTransitionProof> {
        let (old_value, old_proof) = self.prove(key)?;

        let old_root: Hash = self.root;
        self.root = Self::apply_op(
            self.db.as_mut(),
            MerkleTreeOp::Update,
            self.root,
            *key,
            Some(*value),
        )?;

        let (v, proof) = self.prove(key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Update,
            old_root,
            op_proof: old_proof,
            new_root: self.root,
            op_key: *key,
            op_value: *value,
            value: Some(old_value),
            siblings: proof.siblings,
        })
    }

    pub fn delete(&mut self, key: &RawValue) -> TreeResult<MerkleTreeStateTransitionProof> {
        let (value, proof_existence) = self.prove(key)?;

        let old_root: Hash = self.root;
        self.root = Self::apply_op(
            self.db.as_mut(),
            MerkleTreeOp::Delete,
            self.root,
            *key,
            None,
        )?;

        let proof = self.prove_nonexistence(key)?;
        assert!(!proof.existence);

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Delete,
            old_root,
            op_proof: proof,
            new_root: self.root,
            op_key: *key,
            op_value: value,
            value: None,
            siblings: proof_existence.siblings,
        })
    }

    /// returns a proof of existence, which proves that the given key exists in
    /// the tree. It returns the `value` of the leaf at the given `key`, and the
    /// `MerkleProof`.
    pub fn prove(&self, key: &RawValue) -> TreeResult<(RawValue, MerkleProof)> {
        let path = keypath(*key);

        let mut siblings: Vec<Hash> = Vec::new();
        match Self::down(
            self.db.as_ref(),
            (path, 0),
            self.root,
            *key,
            Some(&mut siblings),
            MerkleTreeOp::ReadOnly,
        )? {
            Some((k, v)) if &k == key => Ok((
                v,
                MerkleProof {
                    existence: true,
                    siblings,
                    other_leaf: None,
                },
            )),
            _ => Err(TreeError::key_not_found()),
        }
    }

    /// returns a proof of non-existence, which proves that the given
    /// `key` does not exist in the tree. The return value specifies
    /// the key-value pair in the leaf reached as a result of
    /// resolving `key` as well as a `MerkleProof`.
    pub fn prove_nonexistence(&self, key: &RawValue) -> TreeResult<MerkleProof> {
        let path = keypath(*key);

        let mut siblings: Vec<Hash> = Vec::new();

        // note: non-existence of a key can be in 2 cases:
        match Self::down(
            self.db.as_ref(),
            (path, 0),
            self.root,
            *key,
            Some(&mut siblings),
            MerkleTreeOp::ReadOnly,
        )? {
            // case i) the expected leaf does not exist
            None => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: None,
            }),
            // case ii) the expected leaf does exist in the tree, but it has a different `key`
            Some((k, v)) if &k != key => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: Some((k, v)),
            }),
            _ => Err(TreeError::key_exists()),
        }
        // both cases prove that the given key don't exist in the tree.
    }

    /// verifies an inclusion proof for the given `key` and `value`
    pub fn verify(
        root: Hash,
        proof: &MerkleProof,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<()> {
        let h = proof.compute_root_from_leaf(key, Some(*value))?;

        if h != root {
            Err(TreeError::proof_fail("inclusion".to_string()))
        } else {
            Ok(())
        }
    }

    /// verifies a non-inclusion proof for the given `key`, that is, the given
    /// `key` does not exist in the tree
    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &RawValue) -> TreeResult<()> {
        match proof.other_leaf {
            Some((k, _v)) if &k == key => {
                Err(TreeError::invalid_proof("non-existence".to_string()))
            }
            _ => {
                let k = proof.other_leaf.map(|(k, _)| k).unwrap_or(*key);
                let v: Option<RawValue> = proof.other_leaf.map(|(_, v)| v);
                let h = proof.compute_root_from_leaf(&k, v)?;

                if h != root {
                    Err(TreeError::proof_fail("exclusion".to_string()))
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> TreeResult<()> {
        let mut old_siblings = proof.op_proof.siblings.clone();
        let new_siblings = proof.siblings.clone();

        match proof.op {
            // A deletion is but an insertion subject to a time reversal.
            MerkleTreeOp::Delete => {
                let equivalent_insertion_proof = MerkleTreeStateTransitionProof {
                    op: MerkleTreeOp::Insert,
                    new_root: proof.old_root,
                    old_root: proof.new_root,
                    ..proof.clone()
                };
                Self::verify_state_transition(&equivalent_insertion_proof)
            }
            MerkleTreeOp::Update => {
                if proof.value.is_none() {
                    return Err(TreeError::state_transition_fail(
                        "Invalid proof of update: proof.value should not be None".to_string(),
                    ));
                }
                // check that for the old_root, (op_key, value) *does* exist in the tree
                Self::verify(
                    proof.old_root,
                    &proof.op_proof,
                    &proof.op_key,
                    &proof.value.unwrap(), // unrawp is safe due prev `is_none` check
                )?;
                // check that for the new_root, (op_key, op_value) *does* exist in the tree
                Self::verify(
                    proof.new_root,
                    &MerkleProof {
                        existence: true,
                        siblings: proof.siblings.clone(),
                        other_leaf: None,
                    },
                    &proof.op_key,
                    &proof.op_value,
                )?;

                // All siblings should agree
                (proof.siblings == proof.op_proof.siblings)
                    .then_some(())
                    .ok_or(TreeError::state_transition_fail(format!(
                        "Invalid proof of update for key {}: Siblings don't match.",
                        proof.op_key
                    )))
            }
            MerkleTreeOp::Insert => {
                // check that for the old_root, the new_key does not exist in the tree
                Self::verify_nonexistence(proof.old_root, &proof.op_proof, &proof.op_key)?;

                // check that new_siblings verify with the new_root
                Self::verify(
                    proof.new_root,
                    &MerkleProof {
                        existence: true,
                        siblings: new_siblings.clone(),
                        other_leaf: None,
                    },
                    &proof.op_key,
                    &proof.op_value,
                )?;

                // if other_leaf exists, check path divergence
                if let Some((other_key, _)) = proof.op_proof.other_leaf {
                    let old_path = keypath(other_key);
                    let new_path = keypath(proof.op_key);

                    let divergence_lvl: usize =
                        match zip_eq(old_path, new_path).position(|(x, y)| x != y) {
                            Some(d) => d,
                            None => return Err(TreeError::max_depth()),
                        };

                    if divergence_lvl != new_siblings.len() - 1 {
                        return Err(TreeError::state_transition_fail(
                            "paths divergence does not match".to_string(),
                        ));
                    }
                }

                // let d=divergence_level, assert that:
                // 1) old_siblings[i] == new_siblings[i] ∀ i \ {d}
                // 2) at i==d, if old_siblings[i] != new_siblings[i]:
                //     old_siblings[i] == EMPTY_HASH
                //     new_siblings[i] == old_leaf_hash

                // First rule out the case of insertion into empty tree.
                if new_siblings.is_empty() {
                    return (old_siblings.is_empty() && proof.old_root == EMPTY_HASH)
                        .then_some(())
                        .ok_or(TreeError::state_transition_fail(
                            "new tree has no siblings yet old tree is not the empty tree"
                                .to_string(),
                        ));
                }

                let d = new_siblings.len() - 1;
                old_siblings.resize(d + 1, EMPTY_HASH);
                for i in 0..d {
                    if old_siblings[i] != new_siblings[i] {
                        return Err(TreeError::state_transition_fail(
                            "siblings don't match: old[i]!=new[i] ∀ i (except at i==d)".to_string(),
                        ));
                    }
                }
                if old_siblings[d] != new_siblings[d] {
                    if old_siblings[d] != EMPTY_HASH {
                        return Err(TreeError::state_transition_fail(
                            "siblings don't match: old[d]!=empty".to_string(),
                        ));
                    }
                    let k = proof
                .op_proof
                .other_leaf
                .map(|(k, _)| k)
                .ok_or(TreeError::state_transition_fail(
                        "proof.proof_non_existence.other_leaf can not be empty for the case old_siblings[d]!=new_siblings[d]".to_string()
                        ))?;
                    let v: Option<RawValue> = proof.op_proof.other_leaf.map(|(_, v)| v);
                    let old_leaf_hash = kv_hash(&k, v);
                    if new_siblings[d] != old_leaf_hash {
                        return Err(TreeError::state_transition_fail(
                            "siblings don't match: new[d]!=old_leaf_hash".to_string(),
                        ));
                    }
                }
                Ok(())
            }
            _ => Err(TreeError::invalid_proof("proof.op".to_string())),
        }
    }
}

// auxiliary methods
impl MerkleTree {
    /// Applies given Merkle tree op.
    pub(crate) fn apply_op(
        db: &mut dyn DB,
        op: MerkleTreeOp,
        root: Hash,
        k: RawValue,
        maybe_value: Option<RawValue>,
    ) -> TreeResult<Hash> {
        // Rule out invalid arguments
        match (op, maybe_value) {
            (MerkleTreeOp::Insert, None) | (MerkleTreeOp::Update, None) => {
                Err(TreeError::invalid_state_transition_proof_arg(format!(
                    "{:?} op requires a value argument.",
                    op
                )))
            }
            (MerkleTreeOp::Delete, Some(_)) => {
                Err(TreeError::invalid_state_transition_proof_arg(format!(
                    "{:?} op requires no value argument, yet one was provided.",
                    op
                )))
            }
            (MerkleTreeOp::ReadOnly, _) => {
                Err(TreeError::invalid_state_transition_proof_arg(format!(
                    "{:?} 'read only' op should not reach the 'apply_op' method",
                    op
                )))
            }
            _ => Ok(()),
        }?;

        // go down, update the leaf, go up storing new hashes in the db
        let path = keypath(k);
        let mut siblings: Vec<Hash> = Vec::new();
        let _ = Self::down(
            db,
            (path.clone(), 0), // from lvl 0
            root,
            k,
            Some(&mut siblings),
            op,
        )?;

        let leaf: Leaf = match (op, maybe_value) {
            (MerkleTreeOp::Insert, Some(value)) | (MerkleTreeOp::Update, Some(value)) => {
                Leaf::new(k, value)
            }
            (MerkleTreeOp::Delete, None) => Leaf::new(EMPTY_VALUE, EMPTY_VALUE),
            _ => {
                return Err(TreeError::invalid_state_transition_proof_arg(format!(
                    "{:?} op has invalid value type: {:?}",
                    op, maybe_value
                )))
            }
        };
        let leaf_hash = leaf.hash; // variable to avoid cloning `leaf` later
        db.store_node(Node::Leaf(leaf))?;
        if siblings.is_empty() {
            // return the leaf's hash as root
            return Ok(leaf_hash);
        }

        let new_root = if op == MerkleTreeOp::Delete {
            if siblings.len() == 1 {
                // we're at the root-1 level, there is only a sibling, and we're
                // removing the current leaf.
                // If the sibling is a Leaf, the sibling (leaf) is now the new root
                let sibling_node = db.load_node(siblings[0].into())?;
                if matches!(sibling_node, Node::Leaf(..)) {
                    return Ok(siblings[0]);
                }
                // if the sibling is an Intermediate node, it means that the
                // branch goes deeper, so don't short the path going up and pair
                // it with an empty hash.
                let node = if path[0] {
                    Intermediate::new(siblings[0], EMPTY_HASH)
                } else {
                    Intermediate::new(EMPTY_HASH, siblings[0])
                };
                let node_hash = node.hash; // variable to avoid cloning `node` later

                // store in db
                db.store_node(Node::Intermediate(node))?;
                return Ok(node_hash);
            }
            // use the last sibling as the key that we will push up from
            let l = siblings.len() - 1;
            let remaining_key = siblings[l];
            siblings[l] = EMPTY_HASH;
            // invert the last sibling level
            let mut path = path.clone();
            path[siblings.len() - 1] = !path[siblings.len() - 1];
            Self::up(
                db,
                path,
                siblings.len() - 1,
                remaining_key,
                siblings,
                op,
                true,
            )?
        } else {
            Self::up(db, path, siblings.len() - 1, leaf_hash, siblings, op, true)?
        };

        Ok(new_root)
    }
}

/// Hash function for key-value pairs. Different branch pair hashes to
/// mitigate fake proofs.
pub fn kv_hash(key: &RawValue, value: Option<RawValue>) -> Hash {
    value
        .map(|v| hash_with_flag(F::ONE, &[key.0.to_vec(), v.0.to_vec()].concat()))
        .unwrap_or(EMPTY_HASH)
}

/// Variation of Poseidon hash which takes as input 1 Goldilock element as a
/// flag, and 8 Goldilocks elements as inputs to the hash. Performs the hashing
/// in a single gate.
/// The function is a fork of
/// [hash_n_to_m_no_pad](https://github.com/0xPolygonZero/plonky2/tree/5d9da5a65bbcba2c66eb29c035090eb2e9ccb05f/plonky2/src/hash/hashing.rs#L30)
/// from plonky2.
fn hash_with_flag(flag: F, inputs: &[F]) -> Hash {
    assert_eq!(
        inputs.len(),
        <PoseidonPermutation<F> as PlonkyPermutation<F>>::RATE
    );

    // this will set `perm` to a  `SPONGE_RATE+SPONGE_CAPACITY` (8+4=12) in our
    // case to a vector of repeated `flag` value. Later at the absorption step,
    // it will fit the inputs values at positions 0-8, keeping the flag values
    // at positions 8-12.
    let mut perm = <PoseidonPermutation<F> as PlonkyPermutation<F>>::new(core::iter::repeat(flag));

    // Absorb all input chunks.
    for input_chunk in inputs.chunks(<PoseidonPermutation<F> as PlonkyPermutation<F>>::RATE) {
        perm.set_from_slice(input_chunk, 0);
        perm.permute();
    }

    // Squeeze until we have the desired number of outputs.
    let mut outputs = Vec::new();
    loop {
        for &item in perm.squeeze() {
            outputs.push(item);
            if outputs.len() == NUM_HASH_OUT_ELTS {
                return Hash(crate::middleware::HashOut::from_vec(outputs).elements);
            }
        }
        perm.permute();
    }
}

impl MerkleTree {
    /// returns an iterator over the leaves of the tree
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            state: if self.root == EMPTY_HASH {
                vec![]
            } else {
                vec![self.root]
            },
            db: self.db.as_ref(),
        }
    }
}
impl<'a> IntoIterator for &'a MerkleTree {
    type Item = (RawValue, RawValue);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
pub struct Iter<'a> {
    state: Vec<Hash>,
    db: &'a dyn DB,
}
impl<'a> Iterator for Iter<'a> {
    type Item = (RawValue, RawValue);
    fn next(&mut self) -> Option<Self::Item> {
        let node_hash = self.state.pop()?;

        // Inspect node
        let node = self.db.load_node(node_hash.into()).ok()?;

        match node {
            Node::Leaf(Leaf {
                hash: _,
                path: _,
                key,
                value,
            }) => Some((key, value)),
            Node::Intermediate(Intermediate {
                hash: _,
                left,
                right,
            }) => {
                [right, left].into_iter().for_each(|h| {
                    if h != EMPTY_HASH {
                        self.state.push(h)
                    }
                });
                self.next()
            }
        }
    }
}

impl fmt::Display for MerkleTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "\nPaste in GraphViz (https://dreampuf.github.io/GraphvizOnline/):\n-----"
        )?;
        writeln!(f, "digraph hierarchy {{")?;
        writeln!(f, "node [fontname=Monospace,fontsize=10,shape=box]")?;
        print_graph_viz(f, self.db.as_ref(), self.root)?;
        writeln!(f, "\n}}\n-----")
    }
}

fn print_graph_viz(f: &mut fmt::Formatter<'_>, db: &dyn DB, hash: Hash) -> fmt::Result {
    if hash == EMPTY_HASH {
        return Ok(());
    }

    let node = db.load_node(hash.into()).map_err(|_| fmt::Error)?;
    match node {
        Node::Intermediate(n) => {
            let left_hash: String = if n.left == EMPTY_HASH {
                writeln!(
                    f,
                    "\"{}_child_of_{}\" [label=\"{}\"]",
                    n.left, n.hash, n.left
                )?;
                format!("\"{}_child_of_{}\"", n.left, n.hash)
            } else {
                writeln!(f, "\"{}\"", n.left)?;
                format!("\"{}\"", n.left)
            };
            let right_hash = if n.right == EMPTY_HASH {
                writeln!(
                    f,
                    "\"{}_child_of_{}\" [label=\"{}\"]",
                    n.right, n.hash, n.right
                )?;
                format!("\"{}_child_of_{}\"", n.right, n.hash)
            } else {
                writeln!(f, "\"{}\"", n.right,)?;
                format!("\"{}\"", n.right)
            };
            writeln!(f, "\"{}\" -> {{ {} {} }}", n.hash, left_hash, right_hash,)?;
            print_graph_viz(f, db, n.left)?;
            print_graph_viz(f, db, n.right)
        }
        Node::Leaf(l) => {
            writeln!(f, "\"{}\" [style=filled]", l.hash)?;
            writeln!(f, "\"k:{}\\nv:{}\" [style=dashed]", l.key, l.value)?;
            writeln!(f, "\"{}\" -> {{ \"k:{}\\nv:{}\" }}", l.hash, l.key, l.value,)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MerkleProof {
    // note: currently we don't use the `_existence` field, we would use if we merge the methods
    // `verify` and `verify_nonexistence` into a single one
    #[allow(unused)]
    pub(crate) existence: bool,
    pub(crate) siblings: Vec<Hash>,
    // other_leaf is used for non-existence proofs
    pub(crate) other_leaf: Option<(RawValue, RawValue)>,
}

impl fmt::Display for MerkleProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, s) in self.siblings.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", s)?;
        }
        Ok(())
    }
}

impl MerkleProof {
    /// Computes the root of the Merkle tree suggested by a Merkle proof given a
    /// key & value. If a value is not provided, the terminal node is assumed to
    /// be empty.
    fn compute_root_from_leaf(&self, key: &RawValue, value: Option<RawValue>) -> TreeResult<Hash> {
        let path = keypath(*key);
        let h = kv_hash(key, value);
        self.compute_root_from_node(&h, path)
    }
    fn compute_root_from_node(&self, node_hash: &Hash, path: Vec<bool>) -> TreeResult<Hash> {
        if self.siblings.len() > MAX_DEPTH {
            return Err(TreeError::max_depth());
        }
        let mut h = *node_hash;
        for (i, sibling) in self.siblings.iter().enumerate().rev() {
            let input: Vec<F> = if path[i] {
                [sibling.0, h.0].concat()
            } else {
                [h.0, sibling.0].concat()
            };
            h = hash_with_flag(F::TWO, &input);
        }
        Ok(h)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MerkleClaimAndProof {
    pub root: Hash,
    pub key: RawValue,
    pub value: RawValue,
    pub proof: MerkleProof,
}

impl MerkleClaimAndProof {
    pub fn empty() -> Self {
        Self {
            root: EMPTY_HASH,
            key: EMPTY_VALUE,
            value: EMPTY_VALUE,
            proof: MerkleProof {
                existence: true,
                siblings: vec![],
                other_leaf: None,
            },
        }
    }
    pub fn new(root: Hash, key: RawValue, value: Option<RawValue>, proof: MerkleProof) -> Self {
        Self {
            root,
            key,
            value: value.unwrap_or(EMPTY_VALUE),
            proof,
        }
    }
}

impl fmt::Display for MerkleClaimAndProof {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.proof.fmt(f)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum MerkleTreeOp {
    Insert = 0,
    Update,
    Delete,
    ReadOnly,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MerkleTreeStateTransitionProof {
    pub(crate) op: MerkleTreeOp,

    pub(crate) old_root: Hash,

    /// Insert: proof of non-existence of the op_key for the old_root
    /// Update: proof of existence of (op_key, value) for the old_root
    /// Delete: proof of non-existence of the op_key for the new_root
    pub(crate) op_proof: MerkleProof,

    pub(crate) new_root: Hash,

    /// Key & value relevant to transition proof. These are the
    /// inserted/updated key-value pair for insertions and updates. For
    /// deletions, these are the key-value pair that is deleted.
    pub(crate) op_key: RawValue,
    pub(crate) op_value: RawValue,

    /// Update: value to be replaced.
    pub(crate) value: Option<RawValue>,

    /// Insert: siblings of inserted (op_key, op_value) leading to new_root
    /// Update: siblings of updated (op_key, op_value) leading to new_root
    /// Delete: siblings of deleted (op_key, op_value) leading to old_root
    pub(crate) siblings: Vec<Hash>,
}

impl MerkleTreeStateTransitionProof {
    /// Value used for padding.
    pub fn empty() -> Self {
        let empty_proof_and_claim = MerkleClaimAndProof::empty();
        Self {
            op: MerkleTreeOp::Insert,
            old_root: empty_proof_and_claim.root,
            op_proof: empty_proof_and_claim.proof,
            new_root: empty_proof_and_claim.root,
            op_key: empty_proof_and_claim.key,
            op_value: empty_proof_and_claim.value,
            value: None,
            siblings: vec![],
        }
    }
}

// NOTE: currently we use automatic serialization/deserialization, which is
// used when storing the node into the DB; but we could manually implement it
// for more disk-space efficiency.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Node {
    Leaf(Leaf),
    Intermediate(Intermediate),
}
impl Node {
    pub fn hash(&self) -> Hash {
        match self {
            Node::Leaf(Leaf {
                hash,
                path: _,
                key: _,
                value: _,
            }) => *hash,
            Node::Intermediate(Intermediate {
                hash,
                left: _,
                right: _,
            }) => *hash,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Intermediate {
    hash: Hash,
    left: Hash,
    right: Hash,
}
impl Intermediate {
    fn new(left: Hash, right: Hash) -> Self {
        if left == EMPTY_HASH && right == EMPTY_HASH {
            return Self {
                hash: EMPTY_HASH,
                left,
                right,
            };
        }
        let input: Vec<F> = [left.0.to_vec(), right.0.to_vec()].concat();
        let hash = hash_with_flag(F::TWO, &input);
        Self { hash, left, right }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Leaf {
    pub(crate) hash: Hash,
    pub(crate) path: Vec<bool>,
    pub(crate) key: RawValue,
    pub(crate) value: RawValue,
}
impl Leaf {
    fn new(key: RawValue, value: RawValue) -> Self {
        Self {
            hash: if key == EMPTY_VALUE && value == EMPTY_VALUE {
                // empty node, don't hash {empty, empty} and just use empty as
                // it's hash
                EMPTY_HASH
            } else {
                kv_hash(&key, Some(value))
            },
            path: keypath(key),
            key,
            value,
        }
    }
}

// NOTE 1: think if maybe the length of the returned vector can be <256
// (8*bytes.len()), so that we can do fewer iterations. For example, if the
// tree.max_depth is set to 20, we just need 20 iterations of the loop, not 256.
// NOTE 2: which approach do we take with keys that are longer than the
// max-depth? ie, what happens when two keys share the same path for more bits
// than the max_depth?
/// returns the path of the given key
pub(crate) fn keypath(k: RawValue) -> Vec<bool> {
    let bytes = k.to_bytes();
    debug_assert_eq!(MAX_DEPTH, bytes.len() * 8);
    (0..MAX_DEPTH)
        .map(|n| bytes[n / 8] & (1 << (n % 8)) != 0)
        .collect()
}

#[cfg(test)]
pub mod tests {
    use std::cmp::Ordering;

    use itertools::Itertools;

    use super::*;

    #[test]
    fn test_merkletree() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_merkletree_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_merkletree_opt(db)?;

        Ok(())
    }
    fn test_merkletree_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let mut kvs = HashMap::new();
        for i in 0..8 {
            if i == 1 {
                continue;
            }
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }
        let key = RawValue::from(13);
        let value = RawValue::from(1013);
        kvs.insert(key, value);

        let tree = MerkleTree::new_with_db(db, &kvs);
        // when printing the tree, it should print the same tree as in
        // https://0xparc.github.io/pod2/merkletree.html#example-2
        println!("{}", tree);

        // Inclusion checks
        let (v, proof) = tree.prove(&RawValue::from(13))?;
        assert_eq!(v, RawValue::from(1013));
        println!("{}", proof);

        MerkleTree::verify(tree.root(), &proof, &key, &value)?;

        // Exclusion checks
        let key = RawValue::from(12);
        let proof = tree.prove_nonexistence(&key)?;
        assert_eq!(
            proof.other_leaf.unwrap(),
            (RawValue::from(4), RawValue::from(1004))
        );
        println!("{}", proof);

        MerkleTree::verify_nonexistence(tree.root(), &proof, &key)?;

        let key = RawValue::from(1);
        let proof = tree.prove_nonexistence(&RawValue::from(1))?;
        assert_eq!(proof.other_leaf, None);
        println!("{}", proof);

        MerkleTree::verify_nonexistence(tree.root(), &proof, &key)?;

        // Check iterator
        let collected_kvs: Vec<_> = tree.into_iter().collect::<Vec<_>>();

        // Expected key ordering
        let cmp = |k1, k2| {
            let path1 = keypath(k1);
            let path2 = keypath(k2);

            let first_unequal_bits = std::iter::zip(path1, path2).find(|(b1, b2)| b1 != b2);

            match first_unequal_bits {
                Some((b1, b2)) => {
                    if !b1 & b2 {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
                _ => Ordering::Equal,
            }
        };

        let sorted_kvs = kvs
            .into_iter()
            .sorted_by(|(k1, _), (k2, _)| cmp(*k1, *k2))
            .collect::<Vec<_>>();

        assert_eq!(collected_kvs, sorted_kvs);

        Ok(())
    }

    #[test]
    fn test_delete_to_empty() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_delete_to_empty_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_delete_to_empty_opt(db)?;

        Ok(())
    }
    fn test_delete_to_empty_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let mut tree = MerkleTree::new_with_db(db, &HashMap::new());

        let (key, value) = (RawValue::from(2), RawValue::from(1002));
        let _ = tree.insert(&key, &value)?;

        let (key, value) = (RawValue::from(6), RawValue::from(1006));
        let _ = tree.insert(&key, &value)?;

        let (key, value) = (RawValue::from(3), RawValue::from(1003));
        let _ = tree.insert(&key, &value)?;

        let (key, value) = (RawValue::from(7), RawValue::from(1007));
        let _ = tree.insert(&key, &value)?;

        let _ = tree.delete(&RawValue::from(3))?;
        let _ = tree.delete(&RawValue::from(7))?;
        let _ = tree.delete(&RawValue::from(6))?;
        assert_eq!(
            tree.root,
            Leaf::new(RawValue::from(2), RawValue::from(1002)).hash
        );

        let _ = tree.delete(&RawValue::from(2))?;
        assert_eq!(tree.root, EMPTY_HASH);

        Ok(())
    }

    #[test]
    fn test_prove_verify() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_prove_verify_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_prove_verify_opt(db)?;

        Ok(())
    }
    fn test_prove_verify_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let kvs = [
            (1.into(), 55.into()),
            (2.into(), 88.into()),
            (175.into(), 0.into()),
        ]
        .into_iter()
        .collect();
        let tree = MerkleTree::new_with_db(db, &kvs);

        let (key, value) = (175.into(), 0.into());
        let (v, proof) = tree.prove(&key)?;
        assert_eq!(v, value);
        MerkleTree::verify(tree.root(), &proof, &key, &value)?;

        let (key, value) = (2.into(), 88.into());
        let (v, proof) = tree.prove(&key)?;
        assert_eq!(v, value);
        MerkleTree::verify(tree.root(), &proof, &key, &value)?;

        let (key, value) = (175.into(), 0.into());
        let (v, proof) = tree.prove(&key)?;
        assert_eq!(v, value);
        MerkleTree::verify(tree.root(), &proof, &key, &value)?;

        Ok(())
    }

    #[test]
    fn test_update_leaf() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_update_leaf_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_update_leaf_opt(db)?;

        Ok(())
    }
    fn test_update_leaf_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let kvs = [
            (1.into(), 1.into()),
            (9.into(), 9.into()),
            (7.into(), 7.into()),
            (15.into(), 15.into()),
        ]
        .into_iter()
        .collect();
        let mut tree = MerkleTree::new_with_db(db.clone(), &kvs);
        let state_transition_proof = tree.update(&7.into(), &0.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)?;

        let kvs = [
            (1.into(), 1.into()),
            (9.into(), 9.into()),
            (7.into(), 0.into()),
            (15.into(), 15.into()),
        ]
        .into_iter()
        .collect();
        let tree2 = MerkleTree::new_with_db(db, &kvs);

        assert_eq!(tree.root, tree2.root);

        // update the other leaves
        let state_transition_proof = tree.update(&1.into(), &0.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)?;
        let state_transition_proof = tree.update(&9.into(), &0.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)?;
        let state_transition_proof = tree.update(&15.into(), &0.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)
    }

    #[test]
    fn test_update_delete_leaf() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_update_delete_leaf_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_update_delete_leaf_opt(db)?;

        Ok(())
    }
    fn test_update_delete_leaf_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let kvs: HashMap<RawValue, RawValue> = (0..10)
            .map(|i| (i.into(), i.into()))
            .collect::<HashMap<_, _>>();
        let mut mt = MerkleTree::new_with_db(db, &kvs);

        // insert
        (11..20)
            .map(|i| (i.into(), i.into()))
            .try_for_each(|(k, v)| {
                let mtp = mt.insert(&k, &v).unwrap();
                MerkleTree::verify_state_transition(&mtp)
            })?;
        // update
        (11..20)
            .map(|i| (i.into(), (i + 1).into()))
            .try_for_each(|(k, v)| {
                let mtp = mt.update(&k, &v).unwrap();
                MerkleTree::verify_state_transition(&mtp)
            })?;
        // delete
        (11..20).map(|i| i.into()).try_for_each(|k| {
            let mtp = mt.delete(&k).unwrap();
            MerkleTree::verify_state_transition(&mtp)
        })?;

        Ok(())
    }

    #[test]
    fn test_delete_leaf() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_delete_leaf_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_delete_leaf_opt(db)?;

        Ok(())
    }
    fn test_delete_leaf_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let kvs = [(1.into(), 1.into()), (9.into(), 9.into())]
            .into_iter()
            .collect();
        let tree = MerkleTree::new_with_db(db.clone(), &kvs);
        let expected_root = tree.root;

        let kvs = [
            (1.into(), 1.into()),
            (9.into(), 9.into()),
            (7.into(), 7.into()),
            (15.into(), 15.into()),
        ]
        .into_iter()
        .collect();
        let mut tree = MerkleTree::new_with_db(db.clone(), &kvs);
        let state_transition_proof = tree.delete(&15.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)?;

        let kvs = [
            (1.into(), 1.into()),
            (9.into(), 9.into()),
            (7.into(), 7.into()),
        ]
        .into_iter()
        .collect();
        let tree2 = MerkleTree::new_with_db(db, &kvs);

        assert_eq!(tree.root, tree2.root);

        // delete the leaf '7', which when deleted will leave an entire branch
        // empty
        let state_transition_proof = tree.delete(&7.into())?;
        MerkleTree::verify_state_transition(&state_transition_proof)?;

        assert_eq!(tree.root, expected_root);

        Ok(())
    }

    #[test]
    fn test_delete_from_two_leaves() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_delete_from_two_leaves_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_delete_from_two_leaves_opt(db)?;

        Ok(())
    }
    fn test_delete_from_two_leaves_opt(db: Box<dyn DB>) -> TreeResult<()> {
        // tree with two leaves whose keys diverge at the first bit, so that when
        // deleting one key leads to a tree with a single Leaf as a root
        let mut kvs = HashMap::new();
        kvs.insert(RawValue::from(0), RawValue::from(1000));
        kvs.insert(RawValue::from(1), RawValue::from(1001));

        let mut tree = MerkleTree::new_with_db(db.clone(), &kvs);
        tree.delete(&RawValue::from(1))?;

        // the expected_tree has a single leaf, which should match the tree that
        // started from two leaves and got one removed
        let expected = [(RawValue::from(0), RawValue::from(1000))]
            .into_iter()
            .collect::<HashMap<_, _>>();
        let expected_tree = MerkleTree::new_with_db(db, &expected);

        assert_eq!(tree.root(), expected_tree.root());
        Ok(())
    }

    #[test]
    fn test_state_transition() -> TreeResult<()> {
        let db = Box::new(db::MemDB::new());
        test_state_transition_opt(db)?;

        let db = Box::new(db::rocks::RocksDB::open(
            tempfile::TempDir::new().unwrap().path(),
        )?);
        test_state_transition_opt(db)?;

        Ok(())
    }
    fn test_state_transition_opt(db: Box<dyn DB>) -> TreeResult<()> {
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }

        let mut tree = MerkleTree::new_with_db(db, &kvs);
        let old_root = tree.root();

        // key=37 shares path with key=5, till the level 6, needing 2 extra
        // 'empty' nodes between the original position of key=5 with the new
        // position of key=5 and key=37.
        let key = RawValue::from(37);
        let value = RawValue::from(1037);
        let state_transition_proof = tree.insert(&key, &value)?;

        MerkleTree::verify_state_transition(&state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());
        assert_eq!(state_transition_proof.op_key, key);
        assert_eq!(state_transition_proof.op_value, value);
        assert_eq!(state_transition_proof.value, None);

        // Deleting this key should yield the old tree, and the proof
        // should be the same (mutatis mutandis).
        let mut tree_with_deleted_key = tree.clone();
        let state_transition_proof1 = tree_with_deleted_key.delete(&key)?;
        MerkleTree::verify_state_transition(&state_transition_proof1)?;
        assert_eq!(
            state_transition_proof1.old_root,
            state_transition_proof.new_root
        );
        assert_eq!(
            state_transition_proof1.new_root,
            state_transition_proof.old_root
        );
        assert_eq!(
            state_transition_proof1.op_key,
            state_transition_proof.op_key
        );
        assert_eq!(
            state_transition_proof1.op_value,
            state_transition_proof.op_value
        );
        assert_eq!(
            state_transition_proof1.op_proof,
            state_transition_proof.op_proof
        );
        assert_eq!(
            state_transition_proof1.siblings,
            state_transition_proof.siblings
        );

        // 2nd part of the test. Add a new leaf
        let mut tree_with_another_leaf = tree.clone();
        let key = RawValue::from(21);
        let value = RawValue::from(1021);
        let state_transition_proof = tree_with_another_leaf.insert(&key, &value)?;

        MerkleTree::verify_state_transition(&state_transition_proof)?;

        // Alternatively add this key with another value then update.
        let value1 = RawValue::from(99);
        tree.insert(&key, &value1)?;
        let state_transition_proof1 = tree.update(&key, &value)?;

        MerkleTree::verify_state_transition(&state_transition_proof1)?;

        // `tree` and `tree_with_another_leaf` should coincide.
        assert_eq!(tree.root(), tree_with_another_leaf.root());

        Ok(())
    }
}
