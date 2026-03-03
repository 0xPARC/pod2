//! Module that implements the MerkleTree specified at
//! <https://0xparc.github.io/pod2/merkletree.html> .
use std::{collections::HashMap, fmt, iter::IntoIterator};

use anyhow::Result;
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
use db::{Txn, DB};
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
    // TODO: this method is kept for legacy compatibility at higher levels of
    // the pod2 repo. It should be replaced by the `from_db` or `empty_with_db`
    // or similar, and the `.unwrap()` occurences should be removed.
    pub fn new(kvs: &HashMap<RawValue, RawValue>) -> Self {
        // Start with an empty node as root.

        let db = db::MemDB::new();
        let mut txn = db.begin_txn(true).unwrap();

        // Iterate over key-value pairs (if any) and add them.
        let mut root = EMPTY_HASH;
        txn.store_node(root.into(), Node::Leaf(Leaf::new(root.into(), EMPTY_VALUE)))
            .unwrap();
        for (k, v) in kvs.iter() {
            root = Self::apply_op(&mut txn, MerkleTreeOp::Insert, root, *k, Some(*v)).unwrap();
        }
        txn.commit().unwrap();

        // Fill in hashes.
        Self {
            root,
            db: Box::new(db),
        }
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
    /// which may contain a different key and value than the expected one.
    fn down(
        txn: &Box<dyn Txn>,
        path: Vec<bool>,
        lvl: usize,
        curr_node_hash: Hash, // hash of current level node
        new_key: RawValue,    // key to be added/found at the leaf
        mut siblings: Option<&mut Vec<Hash>>,
        // `get_leaf_only` indicates if want to reach the existing leaf, or keep
        // going down till the virtual divergence. `true` is for read-only
        // operations, while `false` is when the tree is being modified.
        get_leaf_only: bool,
    ) -> Result<Option<(RawValue, RawValue)>> {
        if lvl > MAX_DEPTH {
            panic!("error: max level reached"); // TODO return error
        }

        if curr_node_hash == EMPTY_HASH {
            // return Ok(Some((curr_node_hash.into(), EMPTY_VALUE))); // TODO rm
            return Ok(None);
        }

        let node = txn.load_node(curr_node_hash.into())?;
        match node {
            Node::Intermediate(n) => {
                if path[lvl] {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.left);
                    }
                    Self::down(
                        txn,
                        path,
                        lvl + 1,
                        n.right,
                        new_key,
                        siblings,
                        get_leaf_only,
                    )
                } else {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.right);
                    }
                    Self::down(txn, path, lvl + 1, n.left, new_key, siblings, get_leaf_only)
                }
            }
            Node::Leaf(old_leaf) => {
                dbg!(old_leaf.hash);
                dbg!(old_leaf.key);
                dbg!(old_leaf.value);
                // old_leaf.value is curr_node_hash's value (curr_value)
                if old_leaf.value != EMPTY_VALUE {
                    if get_leaf_only {
                        return Ok(Some((old_leaf.key, old_leaf.value)));
                        // return Ok(Some((curr_node_hash.into(), old_leaf.value)));
                    }

                    if new_key == old_leaf.key {
                        panic!("TODO return err: key already exists");
                    }

                    // dbg rm // TODO rm since this should be always true
                    if old_leaf.hash != curr_node_hash.into() {
                        panic!("AGH");
                    }
                    Self::down_till_divergence(
                        lvl,
                        // old_leaf.key,
                        curr_node_hash.into(),
                        new_key,
                        old_leaf.path,
                        path,
                        siblings.unwrap(), // TODO wip
                    )?;
                    // TODO-NOTE: here we could return the collected siblings for
                    // using them at the highter level tree methods, instead of
                    // recomputing them to get the proofs of existence/nonexistence.
                    // return Ok(Some((old_leaf.key, old_leaf.value)));
                }
                return Ok(Some((old_leaf.key, old_leaf.value)));
            }
            _ => {
                dbg!(&node);
                dbg!("SHOULD NOT BE REACHED");
                Ok(None)
            } // TODO return error since it should not be reached?
        }
    }

    /// goes down through a 'virtual' path till finding a divergence. This
    /// method is used for when adding a new leaf another already existing leaf
    /// is found, so that both leaves (new and old) are pushed down the path
    /// till their keys diverge.
    fn down_till_divergence(
        lvl: usize,
        old_key: RawValue,
        new_key: RawValue,
        old_path: Vec<bool>,
        new_path: Vec<bool>,
        siblings: &mut Vec<Hash>,
    ) -> TreeResult<()> {
        if lvl > MAX_DEPTH {
            panic!("error: max level reached"); // TODO return error
        }
        if old_path[lvl] == new_path[lvl] {
            // siblings.push(old_leaf.hash);
            siblings.push(EMPTY_HASH);
            return Self::down_till_divergence(
                lvl + 1,
                old_key,
                new_key,
                old_path,
                new_path,
                siblings,
            );
        }
        // reached the divergence
        siblings.push(old_key.into());
        Ok(())
    }

    /// go up recursively updating the intermediate nodes
    fn up(
        txn: &mut Box<dyn Txn>,
        path: Vec<bool>,
        curr_lvl: usize,
        key: Hash,
        siblings: Vec<Hash>,
    ) -> Result<Hash> {
        let node = if path[curr_lvl] {
            Intermediate::new(siblings[curr_lvl], key)
        } else {
            Intermediate::new(key, siblings[curr_lvl])
        };
        // store in db
        txn.store_node(node.hash.into(), Node::Intermediate(node.clone()))?;
        // TODO rm clone

        if curr_lvl == 0 {
            return Ok(node.hash);
        }
        Self::up(txn, path, curr_lvl - 1, node.hash.into(), siblings)
    }

    /// returns the value at the given key
    pub fn get(&self, key: &RawValue) -> TreeResult<RawValue> {
        let path = keypath(*key);
        let txn = self.db.begin_txn(false)?;
        let key_resolution = Self::down(&txn, path, 0, self.root, *key, None, true)?;
        match key_resolution {
            Some((k, v)) if &k == key => Ok(v),
            _ => Err(TreeError::key_not_found()),
        }
    }

    /// returns a boolean indicating whether the key exists in the tree
    pub fn contains(&self, key: &RawValue) -> TreeResult<bool> {
        let path = keypath(*key);
        let txn = self.db.begin_txn(false)?;
        match Self::down(&txn, path, 0, self.root, *key, None, true)? {
            Some((k, _)) if &k == key => Ok(true),
            _ => Ok(false),
        }
    }

    pub fn insert(
        &mut self,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<MerkleTreeStateTransitionProof> {
        let mut txn = self.db.begin_txn(true).unwrap();

        let proof_non_existence = self.prove_nonexistence_with_txn(&mut txn, key)?;

        let old_root: Hash = self.root;

        self.root = Self::apply_op(
            &mut txn,
            MerkleTreeOp::Insert,
            self.root,
            *key,
            Some(*value),
        )?;

        let (v, proof) = self.prove_with_txn(&mut txn, key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        txn.commit()?;

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
        let mut txn = self.db.begin_txn(true).unwrap();

        let (old_value, old_proof) = self.prove_with_txn(&mut txn, key)?;

        let old_root: Hash = self.root;
        self.root = Self::apply_op(
            &mut txn,
            MerkleTreeOp::Update,
            self.root,
            *key,
            Some(*value),
        )?;

        let (v, proof) = self.prove_with_txn(&mut txn, key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        txn.commit()?;

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
        let mut txn = self.db.begin_txn(true).unwrap();

        let (value, proof_existence) = self.prove_with_txn(&mut txn, key)?;

        let old_root: Hash = self.root;
        self.root = Self::apply_op(&mut txn, MerkleTreeOp::Delete, self.root, *key, None)?;

        let proof = self.prove_nonexistence_with_txn(&mut txn, key)?;
        assert!(!proof.existence);

        txn.commit()?;

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

    // TODO-NOTE: it may be the case that in some databases we're required to
    // 'discard' the txn in case that we're not committing it.

    /// returns a proof of existence, which proves that the given key exists in
    /// the tree. It returns the `value` of the leaf at the given `key`, and the
    /// `MerkleProof`.
    pub fn prove(&self, key: &RawValue) -> TreeResult<(RawValue, MerkleProof)> {
        let mut txn = self.db.begin_txn(false).unwrap();
        self.prove_with_txn(&mut txn, key)
    }
    pub fn prove_with_txn(
        &self,
        txn: &mut Box<dyn Txn>,
        key: &RawValue,
    ) -> TreeResult<(RawValue, MerkleProof)> {
        let path = keypath(*key);

        let mut siblings: Vec<Hash> = Vec::new();
        match Self::down(txn, path, 0, self.root, *key, Some(&mut siblings), true)? {
            Some((k, v)) if &k == key => Ok((
                v,
                MerkleProof {
                    existence: true,
                    siblings,
                    other_leaf: None,
                },
            )),
            Some((k, v)) if &k != key => panic!("{} - {}", k, key),
            _ => Err(TreeError::key_not_found()),
        }
    }

    /// returns a proof of non-existence, which proves that the given
    /// `key` does not exist in the tree. The return value specifies
    /// the key-value pair in the leaf reached as a result of
    /// resolving `key` as well as a `MerkleProof`.
    pub fn prove_nonexistence(&self, key: &RawValue) -> TreeResult<MerkleProof> {
        let mut txn = self.db.begin_txn(false).unwrap();
        self.prove_nonexistence_with_txn(&mut txn, key)
    }
    pub fn prove_nonexistence_with_txn(
        &self,
        txn: &mut Box<dyn Txn>,
        key: &RawValue,
    ) -> TreeResult<MerkleProof> {
        let path = keypath(*key);

        let mut siblings: Vec<Hash> = Vec::new();

        // note: non-existence of a key can be in 2 cases:
        match Self::down(txn, path, 0, self.root, *key, Some(&mut siblings), true)? {
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
                // check that for the old_root, (op_key, value) *does* exist in the tree
                Self::verify(
                    proof.old_root,
                    &proof.op_proof,
                    &proof.op_key,
                    &proof.value.unwrap(),
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
        }
    }
}

// auxiliary methods
impl MerkleTree {
    /// Applies given Merkle tree op.
    pub(crate) fn apply_op(
        txn: &mut Box<dyn Txn>,
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
            _ => Ok(()),
        }?;

        // TODO-NOTE: when going down/up we can already collect the siblings and return
        // them as 'proof' from this method. This will allow the
        // 'insert,update,delete,prove' methods to avoid computing aside the
        // proof of existence/nonexistence.

        // go down, update the leaf, go up storing new hashes in the db
        let path = keypath(k);
        let mut siblings: Vec<Hash> = Vec::new();
        let _ = Self::down(
            &txn,
            path.clone(),
            0, // from lvl 0
            root.into(),
            k,
            Some(&mut siblings),
            false,
        )?;

        // println!("siblings:");
        // siblings.iter().for_each(|s| println!("{}", s));

        let leaf: Leaf = match (op, maybe_value) {
            (MerkleTreeOp::Insert, Some(value)) | (MerkleTreeOp::Update, Some(value)) => {
                Leaf::new(k, value)
            }
            (MerkleTreeOp::Delete, None) => {
                todo!() // TODO
            }
            _ => panic!("todo err"), // TODO err
        };
        txn.store_node(leaf.hash.into(), Node::Leaf(leaf.clone()))?; // TODO rm clone
        if siblings.len() == 0 {
            // return the leaf's hash as root
            return Ok(leaf.hash);
        }
        let new_root = Self::up(txn, path, siblings.len() - 1, leaf.hash, siblings)?;

        // NOTE-WIP: going up from a delete might need to push upper the leaf in
        // some cases, currently not handled.

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

/*
impl MerkleTree {
    /// returns an iterator over the leaves of the tree
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            state: vec![&self.root.into()],
        }
    }
}
impl<'a> IntoIterator for &'a MerkleTree {
    type Item = (&'a RawValue, &'a RawValue);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
pub struct Iter<'a> {
    state: Vec<&'a Node>,
}
impl<'a> Iterator for Iter<'a> {
    type Item = (&'a RawValue, &'a RawValue);
    fn next(&mut self) -> Option<Self::Item> {
        let node = self.state.pop();
        match node {
            Some(Node::None) => self.next(),
            Some(Node::Leaf(Leaf {
                hash: _,
                path: _,
                key,
                value,
            })) => Some((key, value)),
            Some(Node::Intermediate(Intermediate {
                hash: _,
                left,
                right,
            })) => {
                self.state.push(right);
                self.state.push(left);
                self.next()
            }
            _ => None,
        }
    }
}
*/

impl fmt::Display for MerkleTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let txn = self.db.begin_txn(false).unwrap(); // TODO unwrap

        writeln!(
            f,
            "\nPaste in GraphViz (https://dreampuf.github.io/GraphvizOnline/):\n-----"
        )?;
        writeln!(f, "digraph hierarchy {{")?;
        writeln!(f, "node [fontname=Monospace,fontsize=10,shape=box]")?;
        print_graph_viz(f, &txn, self.root)?;
        // write!(f, "{}", self.root)?;
        writeln!(f, "\n}}\n-----")
    }
}

fn print_graph_viz(f: &mut fmt::Formatter<'_>, txn: &Box<dyn Txn>, hash: Hash) -> fmt::Result {
    if hash == EMPTY_HASH {
        return Ok(());
    }

    let node = txn.load_node(hash.into()).unwrap(); // TODO unwrap
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
            print_graph_viz(f, &txn, n.left)?;
            print_graph_viz(f, &txn, n.right)
        }
        Node::Leaf(l) => {
            writeln!(f, "\"{}\" [style=filled]", l.hash)?;
            writeln!(f, "\"k:{}\\nv:{}\" [style=dashed]", l.key, l.value)?;
            writeln!(f, "\"{}\" -> {{ \"k:{}\\nv:{}\" }}", l.hash, l.key, l.value,)
        }
        Node::None => Ok(()),
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

// TODO-NOTE: currently we use automatic serialization/deserialization, which is
// used when storing the node into the DB; but we could manually implement it
// for more disk-space efficiency.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Node {
    None,
    Leaf(Leaf),
    Intermediate(Intermediate),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intermediate(n) => {
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
                write!(f, "{}", n.left)?;
                write!(f, "{}", n.right)
            }
            Self::Leaf(l) => {
                writeln!(f, "\"{}\" [style=filled]", l.hash)?;
                writeln!(f, "\"k:{}\\nv:{}\" [style=dashed]", l.key, l.value)?;
                writeln!(f, "\"{}\" -> {{ \"k:{}\\nv:{}\" }}", l.hash, l.key, l.value,)
            }
            Self::None => Ok(()),
        }
    }
}

impl Node {
    /*
    fn is_empty(&self) -> bool {
        match self {
            Self::None => true,
            Self::Leaf(_l) => false,
            Self::Intermediate(_n) => false,
        }
    }
    fn is_intermediate(&self) -> bool {
        match self {
            Self::None => false,
            Self::Leaf(_l) => false,
            Self::Intermediate(_n) => true,
        }
    }
    fn hash(&self) -> Hash {
        match self {
            Self::None => EMPTY_HASH,
            Self::Leaf(l) => l.hash,
            Self::Intermediate(n) => n.hash,
        }
    }
    */

    // TODO a variation of this might be needed for the `delete` method
    /*
    /// Normalises a Merkle tree along a specified path. Useful
    /// post-deletion.
    fn normalise_path(&mut self, key_path: &[bool]) {
        match self {
            Self::Leaf(_) | Self::None => (),
            Self::Intermediate(Intermediate {
                hash: _h,
                left,
                right,
            }) => {
                if key_path[0] {
                    right.normalise_path(&key_path[1..]);
                } else {
                    left.normalise_path(&key_path[1..]);
                }

                // If we have a branch with children (NIL, X) or (X,
                // NIL) where X is not a branch, then replace with X.
                if left.is_empty() && !right.is_intermediate() {
                    *self = *right.clone();
                } else if right.is_empty() && !left.is_intermediate() {
                    *self = *left.clone();
                }
            }
        }
    }
    */
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Intermediate {
    hash: Hash,
    left: Hash,
    right: Hash,
}
impl Intermediate {
    fn empty() -> Self {
        Self {
            hash: EMPTY_HASH,
            left: EMPTY_HASH,
            right: EMPTY_HASH,
        }
    }
    fn new(left: Hash, right: Hash) -> Self {
        if left.clone() == EMPTY_HASH && right.clone() == EMPTY_HASH {
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
            hash: kv_hash(&key, Some(value)),
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
    fn test_tmp_merkletree() -> TreeResult<()> {
        let kvs = HashMap::new();
        let mut tree = MerkleTree::new(&kvs);

        let mut txn = tree.db.begin_txn(true).unwrap();

        let (key, value) = (RawValue::from(2), RawValue::from(1002));
        tree.root =
            MerkleTree::apply_op(&mut txn, MerkleTreeOp::Insert, tree.root, key, Some(value))?;

        let (key, value) = (RawValue::from(6), RawValue::from(1006));
        tree.root =
            MerkleTree::apply_op(&mut txn, MerkleTreeOp::Insert, tree.root, key, Some(value))?;

        let (key, value) = (RawValue::from(3), RawValue::from(1003));
        tree.root =
            MerkleTree::apply_op(&mut txn, MerkleTreeOp::Insert, tree.root, key, Some(value))?;

        txn.commit()?;

        println!("{}", tree);

        Ok(())
    }

    #[test]
    fn test_merkletree() -> TreeResult<()> {
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

        let tree = MerkleTree::new(&kvs);
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

        /*
          TODO - this part disabled till tree iterator is ready

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
            .iter()
            .sorted_by(|(k1, _), (k2, _)| cmp(**k1, **k2))
            .collect::<Vec<_>>();

        assert_eq!(collected_kvs, sorted_kvs);
        */

        Ok(())
    }

    #[test]
    fn test_state_transition() -> TreeResult<()> {
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }

        let mut tree = MerkleTree::new(&kvs);
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
