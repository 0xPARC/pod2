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
    hash_fields, Hash, Value, D, EMPTY, F, HASH_SIZE, NULL, VALUE_SIZE,
};
use crate::backends::plonky2::primitives::merkletree::MerkleProof;

pub struct MerkleProofCircuit<const MAX_DEPTH: usize> {
    root: HashOutTarget,
    key: Vec<Target>,
    value: Vec<Target>,
    existence: BoolTarget,
    siblings: Vec<HashOutTarget>,
    // siblings_selectors: Vec<BoolTarget>,
    case_ii_selector: BoolTarget, // for case ii)
    other_key: Vec<Target>,
    other_value: Vec<Target>,
}

impl<const MAX_DEPTH: usize> MerkleProofCircuit<MAX_DEPTH> {
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

        let case_ii_selector = builder.add_virtual_bool_target_safe();
        let other_key = builder.add_virtual_targets(VALUE_SIZE);
        let other_value = builder.add_virtual_targets(VALUE_SIZE);

        // We have 3 cases for when computing the Leaf's hash:
        // - existence: leaf contains the given key & value
        // - non-existence:
        //      - case i) expected leaf does not exist
        //      - case ii) expected leaf does exist but it has a different key
        //
        // The following table expresses the options with their in-circuit
        // selectors:
        // | existence   | case_ii   | leaf_hash                    |
        // | ----------- | --------- | ---------------------------- |
        // | 1           | 0         | H(key, value, 1)             |
        // | 0           | 0         | EMPTY_HASH                   |
        // | 0           | 1         | H(other_key, other_value, 1) |
        // | 1           | 1         | invalid combination          |

        // First, ensure that both existence & case_ii are not true at the same
        // time:
        // 1. sum = existence + case_ii_selector
        let sum = builder.add(existence.target, case_ii_selector.target);
        // 2. sum * (sum-1) == 0
        builder.assert_bool(BoolTarget::new_unsafe(sum));

        // define the case_i_selector as true when both existence and
        // case_ii_selector are false:
        //     case_i_selector = (1 - existence) * (1- case_ii_selector)
        let one = builder.one();
        let existence_inv = builder.sub(one, existence.target);
        let case_ii_inv = builder.sub(one, case_ii_selector.target);
        let case_i_selector = BoolTarget::new_unsafe(builder.mul(existence_inv, case_ii_inv));

        // use (key,value) or (other_key, other_value) depending if it's a proof
        // of existence or of non-existence, ie:
        // k = key * existence + other_key * (1-existence)
        // v = value * existence + other_value * (1-existence)
        let k: Vec<Target> = (0..4)
            .map(|j| builder.select(existence, key[j], other_key[j]))
            .collect();
        let v: Vec<Target> = (0..4)
            .map(|j| builder.select(existence, value[j], other_value[j]))
            .collect();

        // get leaf's hash for the selected k & v
        let h = Self::kv_hash_target(builder, &k, &v);

        // if we're in the case i), use leaf_hash=EMPTY_HASH, else use the
        // previously computed hash h.
        let empty_hash = builder.constant_hash(HashOut::from(NULL.0));
        let leaf_hash = HashOutTarget::from_vec(
            (0..4)
                .map(|j| builder.select(case_i_selector, empty_hash.elements[j], h.elements[j]))
                .collect(),
        );

        // get key's path
        let path = Self::keypath_target(builder, &key);

        // compute the root for the given siblings and the computed leaf_hash
        // (this is for the three cases (existence, non-existence case i, and
        // non-existence case ii)
        let computed_root = Self::compute_root_from_leaf(
            builder, &path, &leaf_hash, &siblings,
            // &siblings_selectors,
        )?;
        // ensure that the computed root matches the given root (which is a
        // public input)
        builder.connect_hashes(computed_root, root);

        Ok(Self {
            existence,
            root,
            siblings,
            key,
            value,
            case_ii_selector,
            other_key,
            other_value,
        })
    }

    /// assigns the given values to the targets
    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        existence: bool,
        root: Hash,
        proof: MerkleProof,
        key: Value,
        value: Value,
    ) -> Result<()> {
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key, &key.0.to_vec())?;
        pw.set_target_arr(&self.value, &value.0.to_vec())?;
        pw.set_bool_target(self.existence, existence)?;

        // pad siblings with zeros to length MAX_DEPTH
        let mut siblings = proof.siblings.clone();
        siblings.resize(MAX_DEPTH, NULL);
        assert_eq!(self.siblings.len(), siblings.len());

        for (i, sibling) in siblings.iter().enumerate() {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()));
        }

        if !existence && proof.other_leaf.is_some() {
            // non-existence case ii) expected leaf does exist but it has a different key
            pw.set_bool_target(self.case_ii_selector, true)?;
            pw.set_target_arr(&self.other_key, &proof.other_leaf.unwrap().0 .0.to_vec())?;
            pw.set_target_arr(&self.other_value, &proof.other_leaf.unwrap().1 .0.to_vec())?;
        } else {
            // existence & non-existence case i) expected leaf does not exist
            pw.set_bool_target(self.case_ii_selector, false)?;
            pw.set_target_arr(&self.other_key, &EMPTY.0.to_vec())?;
            pw.set_target_arr(&self.other_value, &EMPTY.0.to_vec())?;
        }

        Ok(())
    }

    fn compute_root_from_leaf(
        builder: &mut CircuitBuilder<F, D>,
        path: &Vec<BoolTarget>,
        leaf_hash: &HashOutTarget,
        siblings: &Vec<HashOutTarget>,
    ) -> Result<HashOutTarget> {
        assert!(siblings.len() <= MAX_DEPTH);
        // Convenience constants
        let zero = builder.zero();
        let one = builder.one();

        // Generate/constrain sibling selectors
        let sibling_selectors = siblings
            .iter()
            .rev()
            .scan(zero, |cur_selector, sibling| {
                let sibling_is_empty = sibling.elements.iter().fold(builder._true(), |acc, x| {
                    let x_is_zero = builder.is_equal(*x, zero);
                    builder.and(acc, x_is_zero)
                });
                // If there is a sibling, the selector is true, else retain the
                // current selector
                *cur_selector = builder.select(sibling_is_empty, *cur_selector, one);
                Some(BoolTarget::new_unsafe(*cur_selector))
            })
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>();

        let mut h = leaf_hash.clone();
        let one: Target = builder.one(); // constant in-circuit
        for (i, (sibling, selector)) in std::iter::zip(siblings, &sibling_selectors)
            .enumerate()
            .rev()
        {
            // to compute the hash, we want to do the following 3 steps:
            //     Let s := path[i], then
            //     input_1 = sibling * s + h * (1-s) = select(s, sibling, h)
            //     input_2 = sibling * (1-s) + h * s = select(s, h, sibling)
            //     new_h = hash([input_1, input_2])
            // TODO explore if to group multiple muls in a single gate
            let bit: BoolTarget = path[i];
            let input_1: Vec<Target> = (0..4)
                .map(|j| builder.select(bit, sibling.elements[j], h.elements[j]))
                .collect();
            let input_2: Vec<Target> = (0..4)
                .map(|j| builder.select(bit, h.elements[j], sibling.elements[j]))
                .collect();

            let new_h = builder.hash_n_to_hash_no_pad::<PoseidonHash>([input_1, input_2].concat());

            let h_targ: Vec<Target> = (0..4)
                .map(|j| builder.select(*selector, new_h.elements[j], h.elements[j]))
                .collect();
            h = HashOutTarget::from_vec(h_targ);
        }
        Ok(h)
    }

    // Note: this logic is in its own method for easy of reusability but
    // specially to be able to test it isolated.
    fn keypath_target(builder: &mut CircuitBuilder<F, D>, key: &Vec<Target>) -> Vec<BoolTarget> {
        assert_eq!(key.len(), VALUE_SIZE);

        let n_complete_field_elems: usize = MAX_DEPTH / F::BITS;
        let n_extra_bits: usize = MAX_DEPTH - n_complete_field_elems * F::BITS;

        let path: Vec<BoolTarget> = key
            .iter()
            .take(n_complete_field_elems)
            .flat_map(|e| builder.split_le(*e, F::BITS))
            .collect();

        let extra_bits = if n_extra_bits > 0 {
            let extra_bits: Vec<BoolTarget> =
                builder.split_le(key[n_complete_field_elems], F::BITS);
            extra_bits[..n_extra_bits].to_vec()
            // Note: ideally we would do:
            //     let extra_bits = builder.split_le(key[n_complete_field_elems], n_extra_bits);
            // and directly get the extra_bits, but the `split_le` method
            // returns the wrong bits, so currently we get the entire array of
            // bits and crop it at the desired n_extra_bits amount.
        } else {
            vec![]
        };
        [path, extra_bits].concat()
    }

    fn kv_hash_target(
        builder: &mut CircuitBuilder<F, D>,
        key: &Vec<Target>,
        value: &Vec<Target>,
    ) -> HashOutTarget {
        let inputs: Vec<Target> = [key.clone(), value.clone(), vec![builder.one()]].concat();
        builder.hash_n_to_hash_no_pad::<PoseidonHash>(inputs)
    }
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
        test_keypath_opt::<10>()?;
        test_keypath_opt::<16>()?;
        test_keypath_opt::<32>()?;
        test_keypath_opt::<40>()?;
        test_keypath_opt::<64>()?;
        test_keypath_opt::<128>()?;
        test_keypath_opt::<130>()?;
        test_keypath_opt::<250>()?;
        test_keypath_opt::<256>()?;
        Ok(())
    }

    fn test_keypath_opt<const MD: usize>() -> Result<()> {
        for i in 0..5 {
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            let mut pw = PartialWitness::<F>::new();

            let key = Value::from(hash_value(&Value::from(i)));
            let expected_path = keypath(MD, key)?;

            // small circuit logic to check
            // expected_path_targ==keypath_target(key_targ)
            let expected_path_targ: Vec<BoolTarget> = (0..MD)
                .map(|_| builder.add_virtual_bool_target_safe())
                .collect();
            let key_targ = builder.add_virtual_targets(VALUE_SIZE);
            let computed_path_targ =
                MerkleProofCircuit::<MD>::keypath_target(&mut builder, &key_targ);
            for i in 0..MD {
                builder.connect(computed_path_targ[i].target, expected_path_targ[i].target);
            }

            // assign the input values to the targets
            pw.set_target_arr(&key_targ, &key.0.to_vec())?;
            for i in 0..MD {
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

            let computed_h =
                MerkleProofCircuit::<256>::kv_hash_target(&mut builder, &key_targ, &value_targ);
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
    fn test_merkleproof_verify_existence() -> Result<()> {
        test_merkleproof_verify_opt::<10>(true)?;
        test_merkleproof_verify_opt::<16>(true)?;
        test_merkleproof_verify_opt::<32>(true)?;
        test_merkleproof_verify_opt::<40>(true)?;
        test_merkleproof_verify_opt::<64>(true)?;
        test_merkleproof_verify_opt::<128>(true)?;
        test_merkleproof_verify_opt::<130>(true)?;
        test_merkleproof_verify_opt::<250>(true)?;
        test_merkleproof_verify_opt::<256>(true)?;
        Ok(())
    }
    #[test]
    fn test_merkleproof_verify_nonexistence() -> Result<()> {
        test_merkleproof_verify_opt::<10>(false)?;
        test_merkleproof_verify_opt::<16>(false)?;
        test_merkleproof_verify_opt::<32>(false)?;
        test_merkleproof_verify_opt::<40>(false)?;
        test_merkleproof_verify_opt::<64>(false)?;
        test_merkleproof_verify_opt::<128>(false)?;
        test_merkleproof_verify_opt::<130>(false)?;
        test_merkleproof_verify_opt::<250>(false)?;
        test_merkleproof_verify_opt::<256>(false)?;
        Ok(())
    }

    // test logic to be reused both by the existence & nonexistence tests
    fn test_merkleproof_verify_opt<const MD: usize>(existence: bool) -> Result<()> {
        let mut kvs: HashMap<Value, Value> = HashMap::new();
        for i in 0..10 {
            kvs.insert(Value::from(hash_value(&Value::from(i))), Value::from(i));
        }

        let tree = MerkleTree::new(MD, &kvs)?;

        let (key, value, proof) = if existence {
            let key = Value::from(hash_value(&Value::from(5)));
            let (value, proof) = tree.prove(&key)?;
            assert_eq!(value, Value::from(5));
            (key, value, proof)
        } else {
            let key = Value::from(hash_value(&Value::from(200)));
            (key, EMPTY, tree.prove_nonexistence(&key)?)
        };
        assert_eq!(proof.existence, existence);

        if existence {
            MerkleTree::verify(MD, tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(MD, tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofCircuit::<MD>::add_targets(&mut builder)?;
        targets.set_targets(&mut pw, existence, tree.root(), proof, key, value)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_merkletree_edgecases() -> Result<()> {
        // fill the tree as in https://0xparc.github.io/pod2/merkletree.html#example-3
        //
        //     root
        //     /  \
        //    ()  ()
        //   / \  /
        //   0 2 ()
        //        \
        //        ()
        //        /\
        //       5  13

        let mut kvs = HashMap::new();
        kvs.insert(Value::from(0), Value::from(1000));
        kvs.insert(Value::from(2), Value::from(1002));
        kvs.insert(Value::from(5), Value::from(1005));
        kvs.insert(Value::from(13), Value::from(1013));

        const MD: usize = 5;
        let tree = MerkleTree::new(MD, &kvs)?;
        // existence
        test_merkletree_edgecase_opt::<MD>(&tree, Value::from(5))?;
        // non-existence case i) expected leaf does not exist
        test_merkletree_edgecase_opt::<MD>(&tree, Value::from(1))?;
        // non-existence case ii) expected leaf does exist but it has a different 'key'
        test_merkletree_edgecase_opt::<MD>(&tree, Value::from(21))?;

        Ok(())
    }

    fn test_merkletree_edgecase_opt<const MD: usize>(tree: &MerkleTree, key: Value) -> Result<()> {
        let contains = tree.contains(&key)?;
        // generate merkleproof
        let (value, proof) = if contains {
            tree.prove(&key)?
        } else {
            let proof = tree.prove_nonexistence(&key)?;
            (EMPTY, proof)
        };

        assert_eq!(proof.existence, contains);

        // verify the proof (non circuit)
        if proof.existence {
            MerkleTree::verify(MD, tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(MD, tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofCircuit::<MD>::add_targets(&mut builder)?;
        targets.set_targets(&mut pw, proof.existence, tree.root(), proof, key, value)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
