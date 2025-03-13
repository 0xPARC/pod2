#![allow(unused)]
//! Circuits compatible with the merkletree.rs implementation.
use anyhow::{anyhow, Result};
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field, types::Sample},
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, ProverCircuitData, VerifierCircuitData},
        config::Hasher,
        proof::ProofWithPublicInputs,
    },
};
use std::collections::HashMap;
use std::fmt;
use std::iter::IntoIterator;

use crate::backends::counter;
use crate::backends::plonky2::basetypes::{
    hash_fields, Hash, Value, D, F, HASH_SIZE, NULL, VALUE_SIZE,
};
use crate::backends::plonky2::primitives::merkletree::MerkleProof;

// TODO TMP, this might end up being a parameter of the proof struct
const MAX_DEPTH: usize = 256;

// TODO: think if maybe define a ValueTarget type, which to instantiate it
// already performs the checks of length.

pub struct MerkleProofCircuit {
    root: HashOutTarget,
    key: Vec<Target>,
    value: Vec<Target>,
    existence: BoolTarget,
    siblings: Vec<HashOutTarget>,
    siblings_selectors: Vec<BoolTarget>,
    // other_key: Vec<Target>,
    // other_value: Vec<Target>,
}

impl MerkleProofCircuit {
    /// creates the targets and defines the logic of the circuit
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        // create the targets
        let root = builder.add_virtual_hash();
        let key = builder.add_virtual_targets(VALUE_SIZE);
        let value = builder.add_virtual_targets(VALUE_SIZE);
        // from proof struct:
        let existence = builder.add_virtual_bool_target_safe();
        // siblings are padded
        let siblings = builder.add_virtual_hashes(MAX_DEPTH);
        let siblings_selectors = (0..MAX_DEPTH)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();

        // let other_key = builder.add_virtual_targets(VALUE_SIZE);
        // let other_value = builder.add_virtual_targets(VALUE_SIZE);

        // WIP: only covers proof of existence for the moment
        let h = compute_root_from_leaf(builder, &key, &value, &siblings, &siblings_selectors)?;
        builder.connect_hashes(h, root);

        Ok(Self {
            existence,
            root,
            siblings,
            key,
            value,
            // other_key,
            // other_value,
            siblings_selectors,
        })
    }

    /// assigns the given values to the targets
    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        root: Hash,
        proof: MerkleProof,
        key: Value,
        value: Value,
    ) -> Result<()> {
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key, &key.0.to_vec())?;
        pw.set_target_arr(&self.value, &value.0.to_vec())?;
        pw.set_bool_target(self.existence, proof.existence)?;

        // pad siblings
        let mut siblings = proof.siblings.clone();
        siblings.resize(MAX_DEPTH, NULL);
        assert_eq!(self.siblings.len(), siblings.len());

        for (i, sibling) in siblings.iter().enumerate() {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()));
        }
        // The given `siblings` can have length <= MAX_DEPTH, the
        // `siblings_selectors` are used to indicate when the `siblings` exist
        // or if it is padded.
        // `siblings_selectors` are set to `1` when the given siblings exist,
        // and to `0` when the given siblings don't exist.
        for i in 0..proof.siblings.len() {
            pw.set_bool_target(self.siblings_selectors[i], true)?;
        }
        for i in proof.siblings.len()..MAX_DEPTH {
            pw.set_bool_target(self.siblings_selectors[i], false)?;
        }

        // non-existence proof values:
        // pw.set_target_arr(&self.other_key, &proof.other_leaf.0 .0.to_vec())?;
        // pw.set_target_arr(&self.other_value, &proof.other_leaf.1 .0.to_vec())?;

        Ok(())
    }
}

fn compute_root_from_leaf(
    builder: &mut CircuitBuilder<F, D>,
    key: &Vec<Target>,
    value: &Vec<Target>,
    siblings: &Vec<HashOutTarget>,
    siblings_selectors: &Vec<BoolTarget>,
) -> Result<HashOutTarget> {
    assert!(siblings.len() / HASH_SIZE < MAX_DEPTH);
    assert_eq!(siblings_selectors.len(), MAX_DEPTH);

    // get key's path
    let path: Vec<BoolTarget> = key
        .iter()
        .flat_map(|e| builder.split_le(*e, MAX_DEPTH / 4))
        .collect();

    let mut h = kv_hash_target(builder, key, value);

    let one: Target = builder.one(); // constant in-circuit
    for (i, sibling) in siblings.iter().enumerate().rev() {
        // to compute the hash, we want to do the following 3 steps:
        //     Let s := path[i], then
        //     input_1 = sibling * s + h * (1-s)
        //     input_2 = sibling * (1-s) + h * s
        //     new_h = hash([input_1, input_2])

        // TODO group multiple muls in a single gate
        let bit: Target = path[i].target;
        let bit_inv: Target = builder.sub(one, bit);

        let input_1_sibling: Vec<Target> = sibling
            .elements
            .iter()
            .map(|e| builder.mul(*e, bit))
            .collect();
        let input_1_h: Vec<Target> = h
            .elements
            .iter()
            .map(|e| builder.mul(*e, bit_inv))
            .collect();
        let input_1: Vec<Target> = (0..4)
            .map(|j| builder.add(input_1_sibling[j], input_1_h[j]))
            .collect();

        let input_2_sibling: Vec<Target> = sibling
            .elements
            .iter()
            .map(|e| builder.mul(*e, bit_inv))
            .collect();
        let input_2_h: Vec<Target> = h.elements.iter().map(|e| builder.mul(*e, bit)).collect();
        let input_2: Vec<Target> = (0..4)
            .map(|j| builder.add(input_2_sibling[j], input_2_h[j]))
            .collect();

        let new_h = builder.hash_n_to_hash_no_pad::<PoseidonHash>([input_1, input_2].concat());

        // Let s := siblings_selectors[i], then
        // h = new_h * s + h * (1-s)
        let s: Target = siblings_selectors[i].target;
        let s_inv: Target = builder.sub(one, s);
        let new_h_s: Vec<Target> = new_h.elements.iter().map(|e| builder.mul(*e, s)).collect();
        let h_s: Vec<Target> = h.elements.iter().map(|e| builder.mul(*e, s_inv)).collect();
        let h_targ = (0..4).map(|j| builder.add(new_h_s[j], h_s[j])).collect();
        h = HashOutTarget::from_vec(h_targ);
    }
    Ok(h)
}

// Note: this logic is in its own method for easy of reusability but specially
// to be able to test it isolated
fn keypath_target(builder: &mut CircuitBuilder<F, D>, key: &Vec<Target>) -> Vec<BoolTarget> {
    assert_eq!(key.len(), VALUE_SIZE);
    key.iter()
        .flat_map(|e| builder.split_le(*e, F::BITS))
        .collect()
}

fn kv_hash_target(
    builder: &mut CircuitBuilder<F, D>,
    key: &Vec<Target>,
    value: &Vec<Target>,
) -> HashOutTarget {
    let inputs: Vec<Target> = [key.clone(), value.clone(), vec![builder.one()]].concat();
    builder.hash_n_to_hash_no_pad::<PoseidonHash>(inputs)
}

#[cfg(test)]
pub mod tests {
    use itertools::Itertools;
    use std::cmp::Ordering;

    use super::*;
    use crate::backends::plonky2::basetypes::hash_value;
    use crate::backends::plonky2::basetypes::C;
    use crate::backends::plonky2::primitives::merkletree::*;

    #[test]
    fn test_keypath() -> Result<()> {
        for i in 0..10 {
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            let mut pw = PartialWitness::<F>::new();

            let key = Value::from(hash_value(&Value::from(i)));
            let expected_path = keypath(MAX_DEPTH, key)?;

            // small circuit logic to check
            // expected_path_targ==keypath_target(key_targ)
            let expected_path_targ: Vec<BoolTarget> = (0..MAX_DEPTH)
                .map(|_| builder.add_virtual_bool_target_safe())
                .collect();
            let key_targ = builder.add_virtual_targets(VALUE_SIZE);
            let computed_path_targ = keypath_target(&mut builder, &key_targ);
            for i in 0..MAX_DEPTH {
                builder.connect(computed_path_targ[i].target, expected_path_targ[i].target);
            }

            // assign the input values to the targets
            pw.set_target_arr(&key_targ, &key.0.to_vec())?;
            for i in 0..MAX_DEPTH {
                pw.set_bool_target(expected_path_targ[i], expected_path[i])?;
            }

            // generate & verify proof
            let data = builder.build::<C>();
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        }
        Ok(())
    }

    #[test]
    fn test_kv_hash() -> Result<()> {
        for i in 0..10 {
            let key = Value::from(hash_value(&Value::from(i)));
            let value = Value::from(1000 + i);
            let h = kv_hash(&key, Some(value));

            // circuit
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            let mut pw = PartialWitness::<F>::new();

            let h_targ = builder.add_virtual_hash();
            let key_targ = builder.add_virtual_targets(VALUE_SIZE);
            let value_targ = builder.add_virtual_targets(VALUE_SIZE);

            let computed_h = kv_hash_target(&mut builder, &key_targ, &value_targ);
            builder.connect_hashes(computed_h, h_targ);

            // assign the input values to the targets
            pw.set_target_arr(&key_targ, &key.0.to_vec())?;
            pw.set_target_arr(&value_targ, &value.0.to_vec())?;
            pw.set_hash_target(h_targ, HashOut::from_vec(h.0.to_vec()))?;

            // generate & verify proof
            let data = builder.build::<C>();
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        }
        Ok(())
    }

    #[test]
    fn test_merkleproof_verify() -> Result<()> {
        let mut kvs: HashMap<Value, Value> = HashMap::new();
        for i in 0..8 {
            kvs.insert(
                Value::from(hash_value(&Value::from(i))),
                Value::from(1000 + i),
            );
        }

        let tree = MerkleTree::new(32, &kvs)?;

        let key = Value::from(hash_value(&Value::from(5)));
        let (value, proof) = tree.prove(&key)?;
        assert_eq!(value, Value::from(1005));

        MerkleTree::verify(32, tree.root(), &proof, &key, &value)?;

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofCircuit::add_targets(&mut builder)?;
        targets.set_targets(&mut pw, tree.root(), proof, key, value)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
