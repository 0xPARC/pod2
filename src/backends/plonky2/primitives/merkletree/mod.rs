//! Module that implements the MerkleTree specified at
//! https://0xparc.github.io/pod2/merkletree.html .
use std::{collections::HashMap, fmt, iter::IntoIterator};

use itertools::zip_eq;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::middleware::{hash_fields, Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F};

pub mod circuit;
pub use circuit::*;
pub mod error;
pub use error::{TreeError, TreeResult};

/// Implements the MerkleTree specified at
/// https://0xparc.github.io/pod2/merkletree.html
#[derive(Clone, Debug)]
pub struct MerkleTree {
    max_depth: usize,
    root: Node,
}

impl MerkleTree {
    /// builds a new `MerkleTree` where the leaves contain the given key-values
    pub fn new(max_depth: usize, kvs: &HashMap<RawValue, RawValue>) -> TreeResult<Self> {
        // Start with an empty node as root.
        let mut root = Node::None;

        // Iterate over key-value pairs (if any) and add them.
        for (k, v) in kvs.iter() {
            root.apply_op(max_depth, MerkleTreeOp::Insert, *k, Some(*v))?;
        }

        // Fill in hashes.
        let _ = root.compute_hash();
        Ok(Self { max_depth, root })
    }

    /// returns the root of the tree
    pub fn root(&self) -> Hash {
        self.root.hash()
    }

    /// returns the max_depth parameter from the tree
    pub fn max_depth(&self) -> usize {
        self.max_depth
    }

    /// returns the value at the given key
    pub fn get(&self, key: &RawValue) -> TreeResult<RawValue> {
        let path = keypath(self.max_depth, *key)?;
        let (key_resolution, _) = self.root.down(0, self.max_depth, path, None)?;
        match key_resolution {
            Some((k, v)) if &k == key => Ok(v),
            _ => Err(TreeError::key_not_found()),
        }
    }

    /// returns a boolean indicating whether the key exists in the tree
    pub fn contains(&self, key: &RawValue) -> TreeResult<bool> {
        let path = keypath(self.max_depth, *key)?;
        match self.root.down(0, self.max_depth, path, None) {
            Ok((Some((k, _)), _)) => {
                if &k == key {
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        }
    }

    pub fn insert(
        &mut self,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<MerkleTreeStateTransitionProof> {
        let proof_non_existence = self.prove_nonexistence(key)?;

        let old_root: Hash = self.root.hash();
        self.root
            .apply_op(self.max_depth, MerkleTreeOp::Insert, *key, Some(*value))?;
        let new_root = self.root.compute_hash();

        let (v, proof) = self.prove(key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Insert, // insertion
            old_root,
            op_proof: proof_non_existence,
            new_root,
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

        let old_root: Hash = self.root.hash();
        self.root
            .apply_op(self.max_depth, MerkleTreeOp::Update, *key, Some(*value))?;
        let new_root = self.root.compute_hash();

        let (v, proof) = self.prove(key)?;
        assert!(proof.existence);
        assert_eq!(v, *value);
        assert!(proof.other_leaf.is_none());

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Update,
            old_root,
            op_proof: old_proof,
            new_root,
            op_key: *key,
            op_value: *value,
            value: Some(old_value),
            siblings: proof.siblings,
        })
    }

    pub fn delete(&mut self, key: &RawValue) -> TreeResult<MerkleTreeStateTransitionProof> {
        let (value, proof_existence) = self.prove(key)?;

        let old_root: Hash = self.root.hash();
        self.root
            .apply_op(self.max_depth, MerkleTreeOp::Delete, *key, None)?;
        let new_root = self.root.compute_hash();

        let proof = self.prove_nonexistence(key)?;
        assert!(!proof.existence);

        Ok(MerkleTreeStateTransitionProof {
            op: MerkleTreeOp::Delete,
            old_root,
            op_proof: proof,
            new_root,
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
        let path = keypath(self.max_depth, *key)?;

        let mut siblings: Vec<Hash> = Vec::new();

        match self
            .root
            .down(0, self.max_depth, path, Some(&mut siblings))?
        {
            (Some((k, v)), _) if &k == key => Ok((
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
        let path = keypath(self.max_depth, *key)?;

        let mut siblings: Vec<Hash> = Vec::new();

        // note: non-existence of a key can be in 2 cases:
        match self
            .root
            .down(0, self.max_depth, path, Some(&mut siblings))?
        {
            // case i) the expected leaf does not exist
            (None, _) => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: None,
            }),
            // case ii) the expected leaf does exist in the tree, but it has a different `key`
            (Some((k, v)), _) if &k != key => Ok(MerkleProof {
                existence: false,
                siblings,
                other_leaf: Some((k, v)),
            }),
            _ => Err(TreeError::key_not_found()),
        }
        // both cases prove that the given key don't exist in the tree.
    }

    /// verifies an inclusion proof for the given `key` and `value`
    pub fn verify(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<()> {
        let h = proof.compute_root_from_leaf(max_depth, key, Some(*value))?;

        if h != root {
            Err(TreeError::proof_fail("inclusion".to_string()))
        } else {
            Ok(())
        }
    }

    /// verifies a non-inclusion proof for the given `key`, that is, the given
    /// `key` does not exist in the tree
    pub fn verify_nonexistence(
        max_depth: usize,
        root: Hash,
        proof: &MerkleProof,
        key: &RawValue,
    ) -> TreeResult<()> {
        match proof.other_leaf {
            Some((k, _v)) if &k == key => {
                Err(TreeError::invalid_proof("non-existence".to_string()))
            }
            _ => {
                let k = proof.other_leaf.map(|(k, _)| k).unwrap_or(*key);
                let v: Option<RawValue> = proof.other_leaf.map(|(_, v)| v);
                let h = proof.compute_root_from_leaf(max_depth, &k, v)?;

                if h != root {
                    Err(TreeError::proof_fail("exclusion".to_string()))
                } else {
                    Ok(())
                }
            }
        }
    }

    pub fn verify_state_transition(
        max_depth: usize,
        proof: &MerkleTreeStateTransitionProof,
    ) -> TreeResult<()> {
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
                Self::verify_state_transition(max_depth, &equivalent_insertion_proof)
            }
            MerkleTreeOp::Update => {
                // check that for the old_root, (op_key, value) *does* exist in the tree
                Self::verify(
                    max_depth,
                    proof.old_root,
                    &proof.op_proof,
                    &proof.op_key,
                    &proof.value.unwrap(),
                )?;
                // check that for the new_root, (op_key, op_value) *does* exist in the tree
                Self::verify(
                    max_depth,
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
                Self::verify_nonexistence(
                    max_depth,
                    proof.old_root,
                    &proof.op_proof,
                    &proof.op_key,
                )?;

                // check that new_siblings verify with the new_root
                Self::verify(
                    max_depth,
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
                    let old_path = keypath(max_depth, other_key)?;
                    let new_path = keypath(max_depth, proof.op_key)?;

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

    /// returns an iterator over the leaves of the tree
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            state: vec![&self.root],
        }
    }
}

/// Hash function for key-value pairs. Different branch pair hashes to
/// mitigate fake proofs.
pub fn kv_hash(key: &RawValue, value: Option<RawValue>) -> Hash {
    value
        .map(|v| hash_fields(&[key.0.to_vec(), v.0.to_vec(), vec![F::ONE]].concat()))
        .unwrap_or(EMPTY_HASH)
}

impl<'a> IntoIterator for &'a MerkleTree {
    type Item = (&'a RawValue, &'a RawValue);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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
        write!(f, "{}", self.root)?;
        writeln!(f, "\n}}\n-----")
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
    fn compute_root_from_leaf(
        &self,
        max_depth: usize,
        key: &RawValue,
        value: Option<RawValue>,
    ) -> TreeResult<Hash> {
        let path = keypath(max_depth, *key)?;
        let h = kv_hash(key, value);
        self.compute_root_from_node(max_depth, &h, path)
    }
    fn compute_root_from_node(
        &self,
        max_depth: usize,
        node_hash: &Hash,
        path: Vec<bool>,
    ) -> TreeResult<Hash> {
        if self.siblings.len() >= max_depth {
            return Err(TreeError::max_depth());
        }

        let mut h = *node_hash;
        for (i, sibling) in self.siblings.iter().enumerate().rev() {
            let mut input: Vec<F> = if path[i] {
                [sibling.0, h.0].concat()
            } else {
                [h.0, sibling.0].concat()
            };
            input.push(F::TWO);
            h = hash_fields(&input);
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

#[derive(Clone, Debug)]
enum Node {
    None,
    Leaf(Leaf),
    Intermediate(Intermediate),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Intermediate(n) => {
                let left_hash: String = if n.left.is_empty() {
                    writeln!(
                        f,
                        "\"{}_child_of_{}\" [label=\"{}\"]",
                        n.left.hash(),
                        n.hash(),
                        n.left.hash()
                    )?;
                    format!("\"{}_child_of_{}\"", n.left.hash(), n.hash())
                } else {
                    writeln!(f, "\"{}\"", n.left.hash(),)?;
                    format!("\"{}\"", n.left.hash())
                };
                let right_hash = if n.right.is_empty() {
                    writeln!(
                        f,
                        "\"{}_child_of_{}\" [label=\"{}\"]",
                        n.right.hash(),
                        n.hash(),
                        n.right.hash()
                    )?;
                    format!("\"{}_child_of_{}\"", n.right.hash(), n.hash())
                } else {
                    writeln!(f, "\"{}\"", n.right.hash(),)?;
                    format!("\"{}\"", n.right.hash())
                };
                writeln!(f, "\"{}\" -> {{ {} {} }}", n.hash(), left_hash, right_hash,)?;
                write!(f, "{}", n.left)?;
                write!(f, "{}", n.right)
            }
            Self::Leaf(l) => {
                writeln!(f, "\"{}\" [style=filled]", l.hash())?;
                writeln!(f, "\"k:{}\\nv:{}\" [style=dashed]", l.key, l.value)?;
                writeln!(
                    f,
                    "\"{}\" -> {{ \"k:{}\\nv:{}\" }}",
                    l.hash(),
                    l.key,
                    l.value,
                )
            }
            Self::None => Ok(()),
        }
    }
}

impl Node {
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
    fn compute_hash(&mut self) -> Hash {
        match self {
            Self::None => EMPTY_HASH,
            Self::Leaf(l) => l.compute_hash(),
            Self::Intermediate(n) => n.compute_hash(),
        }
    }
    fn hash(&self) -> Hash {
        match self {
            Self::None => EMPTY_HASH,
            Self::Leaf(l) => l.hash(),
            Self::Intermediate(n) => n.hash(),
        }
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
        &self,
        lvl: usize,
        max_depth: usize,
        path: Vec<bool>,
        mut siblings: Option<&mut Vec<Hash>>,
    ) -> TreeResult<(Option<(RawValue, RawValue)>, usize)> {
        if lvl >= max_depth {
            return Err(TreeError::max_depth());
        }

        match self {
            Self::Intermediate(n) => {
                if path[lvl] {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.left.hash());
                    }
                    n.right.down(lvl + 1, max_depth, path, siblings)
                } else {
                    if let Some(s) = siblings.as_mut() {
                        s.push(n.right.hash());
                    }
                    n.left.down(lvl + 1, max_depth, path, siblings)
                }
            }
            Self::Leaf(Leaf {
                key,
                value,
                path: _p,
                hash: _h,
            }) => Ok((Some((*key, *value)), lvl)),
            _ => Ok((None, lvl)),
        }
    }

    /// Applies given Merkle tree op without computing hashes.
    pub(crate) fn apply_op(
        &mut self,
        max_depth: usize,
        op: MerkleTreeOp,
        key: RawValue,
        maybe_value: Option<RawValue>,
    ) -> TreeResult<()> {
        let key_path = keypath(max_depth, key)?;
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

        // Loop through to leaf.
        self.apply_op_loop(0, max_depth, op, key, &key_path, maybe_value)?;

        // If we are dealing with a deletion, normalise along key
        // path.
        if let MerkleTreeOp::Delete = op {
            self.normalise_path(&key_path);
        }

        Ok(())
    }

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

    fn apply_op_loop(
        &mut self,
        lvl: usize,
        max_depth: usize,
        op: MerkleTreeOp,
        key: RawValue,
        key_path: &[bool],
        maybe_value: Option<RawValue>,
    ) -> TreeResult<()> {
        if lvl >= max_depth {
            return Err(TreeError::max_depth());
        }

        match self {
            Self::Intermediate(n) => {
                if key_path[lvl] {
                    n.right
                        .apply_op_loop(lvl + 1, max_depth, op, key, key_path, maybe_value)
                } else {
                    n.left
                        .apply_op_loop(lvl + 1, max_depth, op, key, key_path, maybe_value)
                }
            }
            _ => {
                *self = Self::op_node_check(max_depth, lvl, self, op, key, key_path, maybe_value)?;
                Ok(())
            }
        }
    }

    /// Checks the terminal node against the desired op and returns a
    /// suitable replacement.
    ///
    /// - Insertion => Node should be empty or contain a different
    ///   key. A leaf is inserted in the right place.
    /// - Update/Deletion => Node should contain the given key. The
    ///   value is replaced in the case of an update and the leaf removed
    ///   in the case of a deletion.
    pub(crate) fn op_node_check(
        max_depth: usize,
        lvl: usize,
        node: &Node,
        op: MerkleTreeOp,
        key: RawValue,
        key_path: &[bool],
        maybe_value: Option<RawValue>,
    ) -> TreeResult<Node> {
        use MerkleTreeOp::*;

        // Invalid args are assumed to have been ruled out.
        match (op, node, maybe_value) {
            // Insertion case
            (Insert, Node::None, Some(value)) => Ok(Node::Leaf(Leaf::new(max_depth, key, value)?)),
            (Insert, Node::Leaf(l), Some(value)) => {
                // in this case, it means that we found a leaf in the new-leaf
                // path, thus we need to push both leaves (old-leaf and
                // new-leaf) down the path till their paths diverge.

                // first check that keys of both leaves are different
                // (l=old-leaf, leaf=new-leaf)
                if l.key == key {
                    // Note: current approach returns an error when trying to
                    // add to a leaf where the key already exists. We could also
                    // ignore it if needed.
                    Err(TreeError::key_exists())
                } else {
                    let old_leaf = l.clone();
                    // set new node as an intermediate node
                    let mut new_node = Node::Intermediate(Intermediate::empty());
                    new_node.down_till_divergence(
                        lvl,
                        max_depth,
                        old_leaf,
                        Leaf {
                            hash: None,
                            path: key_path.to_vec(),
                            key,
                            value,
                        },
                    )?;
                    Ok(new_node)
                }
            }
            // Update case
            (Update, Node::Leaf(l), Some(value)) if l.key == key => {
                Ok(Node::Leaf(Leaf::new(max_depth, key, value)?))
            }
            // Deletion case
            (Delete, Node::Leaf(l), None) if l.key == key => Ok(Node::None),
            // Case of terminal node that does not match.
            _ => Err(TreeError::state_transition_fail(format!(
                "{:?} op requires key {} to be present in the tree, yet it is not.",
                op, key
            ))),
        }
    }

    /// goes down through a 'virtual' path till finding a divergence. This
    /// method is used for when adding a new leaf another already existing leaf
    /// is found, so that both leaves (new and old) are pushed down the path
    /// till their keys diverge.
    fn down_till_divergence(
        &mut self,
        lvl: usize,
        max_depth: usize,
        old_leaf: Leaf,
        new_leaf: Leaf,
    ) -> TreeResult<()> {
        if lvl >= max_depth {
            return Err(TreeError::max_depth());
        }

        if let Node::Intermediate(ref mut n) = self {
            if old_leaf.path[lvl] != new_leaf.path[lvl] {
                // reached divergence in next level, set the leaves as children
                // at the current node
                if new_leaf.path[lvl] {
                    n.left = Box::new(Node::Leaf(old_leaf));
                    n.right = Box::new(Node::Leaf(new_leaf));
                } else {
                    n.left = Box::new(Node::Leaf(new_leaf));
                    n.right = Box::new(Node::Leaf(old_leaf));
                }
                return Ok(());
            }

            // no divergence yet, continue going down
            if new_leaf.path[lvl] {
                n.right = Box::new(Node::Intermediate(Intermediate::empty()));
                return n
                    .right
                    .down_till_divergence(lvl + 1, max_depth, old_leaf, new_leaf);
            } else {
                n.left = Box::new(Node::Intermediate(Intermediate::empty()));
                return n
                    .left
                    .down_till_divergence(lvl + 1, max_depth, old_leaf, new_leaf);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct Intermediate {
    hash: Option<Hash>,
    left: Box<Node>,
    right: Box<Node>,
}
impl Intermediate {
    fn empty() -> Self {
        Self {
            hash: None,
            left: Box::new(Node::None),
            right: Box::new(Node::None),
        }
    }
    fn compute_hash(&mut self) -> Hash {
        if self.left.clone().is_empty() && self.right.clone().is_empty() {
            self.hash = Some(EMPTY_HASH);
            return EMPTY_HASH;
        }
        let l_hash = self.left.compute_hash();
        let r_hash = self.right.compute_hash();
        let input: Vec<F> = [l_hash.0.to_vec(), r_hash.0.to_vec(), vec![F::TWO]].concat();
        let h = hash_fields(&input);
        self.hash = Some(h);
        h
    }
    fn hash(&self) -> Hash {
        self.hash.expect("Hash has not been computed.")
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Leaf {
    pub(crate) hash: Option<Hash>,
    pub(crate) path: Vec<bool>,
    pub(crate) key: RawValue,
    pub(crate) value: RawValue,
}
impl Leaf {
    fn new(max_depth: usize, key: RawValue, value: RawValue) -> TreeResult<Self> {
        Ok(Self {
            hash: None,
            path: keypath(max_depth, key)?,
            key,
            value,
        })
    }
    fn compute_hash(&mut self) -> Hash {
        let h = kv_hash(&self.key, Some(self.value));
        self.hash = Some(h);
        h
    }
    fn hash(&self) -> Hash {
        self.hash.expect("Hash has not been computed.")
    }
}

// NOTE 1: think if maybe the length of the returned vector can be <256
// (8*bytes.len()), so that we can do fewer iterations. For example, if the
// tree.max_depth is set to 20, we just need 20 iterations of the loop, not 256.
// NOTE 2: which approach do we take with keys that are longer than the
// max-depth? ie, what happens when two keys share the same path for more bits
// than the max_depth?
/// returns the path of the given key
pub(crate) fn keypath(max_depth: usize, k: RawValue) -> TreeResult<Vec<bool>> {
    let bytes = k.to_bytes();
    if max_depth > 8 * bytes.len() {
        // note that our current keys are of Value type, which are 4 Goldilocks
        // field elements, ie ~256 bits, therefore the max_depth can not be
        // bigger than 256.
        return Err(TreeError::too_short_key(8 * bytes.len(), max_depth));
    }
    Ok((0..max_depth)
        .map(|n| bytes[n / 8] & (1 << (n % 8)) != 0)
        .collect())
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

#[cfg(test)]
pub mod tests {
    use std::cmp::Ordering;

    use itertools::Itertools;

    use super::*;

    #[test]
    fn test_merkletree() -> TreeResult<()> {
        let max_depth: usize = 32;
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

        let tree = MerkleTree::new(max_depth, &kvs)?;
        // when printing the tree, it should print the same tree as in
        // https://0xparc.github.io/pod2/merkletree.html#example-2
        println!("{}", tree);

        // Inclusion checks
        let (v, proof) = tree.prove(&RawValue::from(13))?;
        assert_eq!(v, RawValue::from(1013));
        println!("{}", proof);

        MerkleTree::verify(max_depth, tree.root(), &proof, &key, &value)?;

        // Exclusion checks
        let key = RawValue::from(12);
        let proof = tree.prove_nonexistence(&key)?;
        assert_eq!(
            proof.other_leaf.unwrap(),
            (RawValue::from(4), RawValue::from(1004))
        );
        println!("{}", proof);

        MerkleTree::verify_nonexistence(max_depth, tree.root(), &proof, &key)?;

        let key = RawValue::from(1);
        let proof = tree.prove_nonexistence(&RawValue::from(1))?;
        assert_eq!(proof.other_leaf, None);
        println!("{}", proof);

        MerkleTree::verify_nonexistence(max_depth, tree.root(), &proof, &key)?;

        // Check iterator
        let collected_kvs: Vec<_> = tree.into_iter().collect::<Vec<_>>();

        // Expected key ordering
        let cmp = |max_depth: usize| {
            move |k1, k2| {
                let path1 = keypath(max_depth, k1).unwrap();
                let path2 = keypath(max_depth, k2).unwrap();

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
            }
        };

        let sorted_kvs = kvs
            .iter()
            .sorted_by(|(k1, _), (k2, _)| cmp(max_depth)(**k1, **k2))
            .collect::<Vec<_>>();

        assert_eq!(collected_kvs, sorted_kvs);

        Ok(())
    }

    #[test]
    fn test_state_transition() -> TreeResult<()> {
        let max_depth: usize = 32;
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }

        let mut tree = MerkleTree::new(max_depth, &kvs)?;
        let old_root = tree.root();

        // key=37 shares path with key=5, till the level 6, needing 2 extra
        // 'empty' nodes between the original position of key=5 with the new
        // position of key=5 and key=37.
        let key = RawValue::from(37);
        let value = RawValue::from(1037);
        let state_transition_proof = tree.insert(&key, &value)?;

        MerkleTree::verify_state_transition(max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());
        assert_eq!(state_transition_proof.op_key, key);
        assert_eq!(state_transition_proof.op_value, value);
        assert_eq!(state_transition_proof.value, None);

        // Deleting this key should yield the old tree, and the proof
        // should be the same (mutatis mutandis).
        let mut tree_with_deleted_key = tree.clone();
        let state_transition_proof1 = tree_with_deleted_key.delete(&key)?;
        MerkleTree::verify_state_transition(max_depth, &state_transition_proof1)?;
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

        MerkleTree::verify_state_transition(max_depth, &state_transition_proof)?;

        // Alternatively add this key with another value then update.
        let value1 = RawValue::from(99);
        tree.insert(&key, &value1)?;
        let state_transition_proof1 = tree.update(&key, &value)?;

        MerkleTree::verify_state_transition(max_depth, &state_transition_proof1)?;

        // `tree` and `tree_with_another_leaf` should coincide.
        assert_eq!(tree.root(), tree_with_another_leaf.root());

        Ok(())
    }
}
