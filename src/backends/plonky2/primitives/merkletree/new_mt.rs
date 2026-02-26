use std::{any::Any, collections::HashMap, fmt, iter::IntoIterator};

use anyhow::Result;
use dyn_clone::DynClone;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::NUM_HASH_OUT_ELTS, hashing::PlonkyPermutation, poseidon::PoseidonPermutation,
    },
};

pub use super::error::{TreeError, TreeResult};
use crate::middleware::{EqualsAny, Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F};

struct Intermediate {
    left_hash: Hash,
    right_hash: Hash,
}

impl Intermediate {
    fn hash(&self) -> Hash {
        let input: Vec<F> = [self.left_hash.0.to_vec(), self.right_hash.0.to_vec()].concat();
        hash_with_flag(F::TWO, &input)
    }
    fn new(left_hash: Hash, right_hash: Hash) -> Self {
        Self {
            left_hash,
            right_hash,
        }
    }
}

struct Leaf {
    path: Vec<bool>,
    key: RawValue,
    value: RawValue,
}

#[derive(Debug, Clone)]
enum Node {
    None,
    Leaf { key: RawValue, value: RawValue },
    Intermediate { left: Hash, right: Hash },
}

impl Node {
    fn hash(&self) -> Hash {
        match self {
            Node::None => EMPTY_HASH,
            Node::Leaf { key, value } => {
                hash_with_flag(F::ONE, &[key.0.to_vec(), value.0.to_vec()].concat())
            }
            Node::Intermediate { left, right } => {
                let input: Vec<F> = [left.0.to_vec(), right.0.to_vec()].concat();
                hash_with_flag(F::TWO, &input)
            }
        }
    }
}

trait Database: fmt::Debug + DynClone + Sync + Send + Any + EqualsAny {
    fn load_node(&self, hash: Hash) -> Result<Node>;
    fn store_node(&self, hash: Hash, node: Node) -> Result<()>;
}
dyn_clone::clone_trait_object!(Database);

#[derive(Clone, Debug)]
pub struct MerkleTree {
    root: Hash,
    db: Box<dyn Database>,
}

impl MerkleTree {
    /// builds a new `MerkleTree` where the leaves contain the given key-values
    pub fn new(kvs: &HashMap<RawValue, RawValue>) -> Self {
        todo!()
    }

    pub fn empty_with_db(db: Box<dyn Database>) -> Self {
        Self::from_db(EMPTY_HASH, db)
    }

    pub fn from_db(root: Hash, db: Box<dyn Database>) -> Self {
        Self { root, db }
    }

    /// returns the root of the tree
    pub fn root(&self) -> Hash {
        self.root
    }

    /// returns the value at the given key
    pub fn get(&self, key: &RawValue) -> TreeResult<RawValue> {
        todo!()
    }

    /// returns a boolean indicating whether the key exists in the tree
    pub fn contains(&self, key: &RawValue) -> TreeResult<bool> {
        todo!()
    }

    /*
    pub fn insert(
        &mut self,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<MerkleTreeStateTransitionProof> {
        todo!()
    }
    */

    fn _insert(&mut self, key: &RawValue, value: &RawValue) -> TreeResult<()> {
        todo!()
    }
    fn insert_recursive(
        &self,
        node: Node,
        lvl: usize,
        key_path: &[bool],
        key: &RawValue,
        value: &RawValue,
    ) -> Result<Node> {
        let node = match node {
            Node::Intermediate { left, right } => {
                let child_hash = if key_path[lvl] { right } else { left };
                let child_node = self.db.load_node(child_hash)?;
                let child_node =
                    self.insert_recursive(child_node, lvl + 1, key_path, key, value)?;
                if key_path[lvl] {
                    Node::Intermediate {
                        left: child_node.hash(),
                        right,
                    }
                } else {
                    Node::Intermediate {
                        left,
                        right: child_node.hash(),
                    }
                }
            }
            Node::None => Node::Leaf {
                key: key.clone(),
                value: value.clone(),
            },
            Node::Leaf { key, value } => {
                todo!()
            }
        };
        self.db.store_node(node.hash(), node.clone())?;
        Ok(node)
    }

    fn _update(&mut self, key: &RawValue, value: &RawValue) -> TreeResult<()> {
        todo!()
    }

    fn _delete(&mut self, key: &RawValue) -> TreeResult<()> {
        todo!()
    }

    /*
    /// returns a proof of existence, which proves that the given key exists in
    /// the tree. It returns the `value` of the leaf at the given `key`, and the
    /// `MerkleProof`.
    pub fn prove(&self, key: &RawValue) -> TreeResult<(RawValue, MerkleProof)> {
        todo!()
    }

    /// returns a proof of non-existence, which proves that the given
    /// `key` does not exist in the tree. The return value specifies
    /// the key-value pair in the leaf reached as a result of
    /// resolving `key` as well as a `MerkleProof`.
    pub fn prove_nonexistence(&self, key: &RawValue) -> TreeResult<MerkleProof> {
        todo!()
    }

    /// verifies an inclusion proof for the given `key` and `value`
    pub fn verify(
        root: Hash,
        proof: &MerkleProof,
        key: &RawValue,
        value: &RawValue,
    ) -> TreeResult<()> {
        todo!()
    }

    pub fn verify_nonexistence(root: Hash, proof: &MerkleProof, key: &RawValue) -> TreeResult<()> {
        todo!()
    }

    pub fn verify_state_transition(proof: &MerkleTreeStateTransitionProof) -> TreeResult<()> {
        todo!()
    }
    */

    pub fn iter(&self) -> Iter<'_> {
        todo!()
    }
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
