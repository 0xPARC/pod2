//! Circuits compatible with the merkletree.rs implementation. This module
//! offers two different circuits:
//!
//! - `MerkleProofCircuit`: allows to verify both proofs of existence and proofs
//! non-existence with the same circuit.
//! - `MerkleProofExistenceCircuit`: allows to verify proofs of existence only.
//!
//! If only proofs of existence are needed, use `MerkleProofExistenceCircuit`,
//! which requires less amount of constraints than `MerkleProofCircuit`.
//!
use anyhow::Result;
use plonky2::{
    field::types::Field,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use std::iter;

use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::primitives::merkletree::MerkleProof;

/// `MerkleProofCircuit` allows to verify both proofs of existence and proofs
/// non-existence with the same circuit.
/// If only proofs of existence are needed, use `MerkleProofExistenceCircuit`,
/// which requires less amount of constraints.
pub struct MerkleProofCircuit<const MAX_DEPTH: usize> {
    pub root: HashOutTarget,
    pub key: ValueTarget,
    pub value: ValueTarget,
    pub existence: BoolTarget,
    pub siblings: Vec<HashOutTarget>,
    pub case_ii_selector: BoolTarget, // for case ii)
    pub other_key: ValueTarget,
    pub other_value: ValueTarget,
}

impl<const MAX_DEPTH: usize> MerkleProofCircuit<MAX_DEPTH> {
    /// creates the targets and defines the logic of the circuit
    pub fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        // create the targets
        let key = builder.add_virtual_value();
        let value = builder.add_virtual_value();
        // from proof struct:
        let existence = builder.add_virtual_bool_target_safe();
        // siblings are padded till MAX_DEPTH length
        let siblings = builder.add_virtual_hashes(MAX_DEPTH);

        let case_ii_selector = builder.add_virtual_bool_target_safe();
        let other_key = builder.add_virtual_value();
        let other_value = builder.add_virtual_value();

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
        let not_existence = builder.not(existence);
        let not_case_ii_selector = builder.not(case_ii_selector);
        let case_i_selector = builder.and(not_existence, not_case_ii_selector);

        // use (key,value) or (other_key, other_value) depending if it's a proof
        // of existence or of non-existence, ie:
        // k = key * existence + other_key * (1-existence)
        // v = value * existence + other_value * (1-existence)
        let k = builder.select_value(existence, key, other_key);
        let v = builder.select_value(existence, value, other_value);

        // get leaf's hash for the selected k & v
        let h = kv_hash_target(builder, &k, &v);

        // if we're in the case i), use leaf_hash=EMPTY_HASH, else use the
        // previously computed hash h.
        let empty_hash = builder.constant_hash(HashOut::from(EMPTY_HASH.0));
        let leaf_hash = HashOutTarget::from_vec(
            (0..4)
                .map(|j| builder.select(case_i_selector, empty_hash.elements[j], h.elements[j]))
                .collect(),
        );

        // get key's path
        let path = keypath_target::<MAX_DEPTH>(builder, &key);

        // compute the root for the given siblings and the computed leaf_hash
        // (this is for the three cases (existence, non-existence case i, and
        // non-existence case ii).
        // This root will be assigned in the `set_targets` method, and it is a
        // public input.
        let root = compute_root_from_leaf::<MAX_DEPTH>(builder, &path, &leaf_hash, &siblings)?;

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
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        existence: bool,
        root: Hash,
        proof: MerkleProof,
        key: Value,
        value: Value,
    ) -> Result<()> {
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &key.0)?;
        pw.set_target_arr(&self.value.elements, &value.0)?;
        pw.set_bool_target(self.existence, existence)?;

        // pad siblings with zeros to length MAX_DEPTH
        let mut siblings = proof.siblings.clone();
        siblings.resize(MAX_DEPTH, EMPTY_HASH);
        assert_eq!(self.siblings.len(), siblings.len());

        for (i, sibling) in siblings.iter().enumerate() {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()))?;
        }

        match proof.other_leaf {
            Some((k, v)) if !existence => {
                // non-existence case ii) expected leaf does exist but it has a different key
                pw.set_bool_target(self.case_ii_selector, true)?;
                pw.set_target_arr(&self.other_key.elements, &k.0)?;
                pw.set_target_arr(&self.other_value.elements, &v.0)?;
            }
            _ => {
                // existence & non-existence case i) expected leaf does not exist
                pw.set_bool_target(self.case_ii_selector, false)?;
                pw.set_target_arr(&self.other_key.elements, &EMPTY_VALUE.0)?;
                pw.set_target_arr(&self.other_value.elements, &EMPTY_VALUE.0)?;
            }
        }

        Ok(())
    }
}

/// `MerkleProofExistenceCircuit` allows to verify proofs of existence only. If
/// proofs of non-existence are needed, use `MerkleProofCircuit`.
pub struct MerkleProofExistenceCircuit<const MAX_DEPTH: usize> {
    pub root: HashOutTarget,
    pub key: ValueTarget,
    pub value: ValueTarget,
    pub siblings: Vec<HashOutTarget>,
}

impl<const MAX_DEPTH: usize> MerkleProofExistenceCircuit<MAX_DEPTH> {
    /// creates the targets and defines the logic of the circuit
    pub fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        // create the targets
        let key = builder.add_virtual_value();
        let value = builder.add_virtual_value();
        // siblings are padded till MAX_DEPTH length
        let siblings = builder.add_virtual_hashes(MAX_DEPTH);

        // get leaf's hash for the selected k & v
        let leaf_hash = kv_hash_target(builder, &key, &value);

        // get key's path
        let path = keypath_target::<MAX_DEPTH>(builder, &key);

        // compute the root for the given siblings and the computed leaf_hash.
        // This root will be assigned in the `set_targets` method, and it is a
        // public input.
        let root = compute_root_from_leaf::<MAX_DEPTH>(builder, &path, &leaf_hash, &siblings)?;

        Ok(Self {
            root,
            siblings,
            key,
            value,
        })
    }

    /// assigns the given values to the targets
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        root: Hash,
        proof: MerkleProof,
        key: Value,
        value: Value,
    ) -> Result<()> {
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &key.0)?;
        pw.set_target_arr(&self.value.elements, &value.0)?;

        // pad siblings with zeros to length MAX_DEPTH
        let mut siblings = proof.siblings.clone();
        siblings.resize(MAX_DEPTH, EMPTY_HASH);
        assert_eq!(self.siblings.len(), siblings.len());

        for (i, sibling) in siblings.iter().enumerate() {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()))?;
        }

        Ok(())
    }
}

fn compute_root_from_leaf<const MAX_DEPTH: usize>(
    builder: &mut CircuitBuilder<F, D>,
    path: &Vec<BoolTarget>,
    leaf_hash: &HashOutTarget,
    siblings: &Vec<HashOutTarget>,
) -> Result<HashOutTarget> {
    assert_eq!(siblings.len(), MAX_DEPTH);
    // Convenience constants
    let zero = builder.zero();
    let one = builder.one();
    let two = builder.two();

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
        let input_1: Vec<Target> = (0..4)
            .map(|j| builder.select(path[i], sibling.elements[j], h.elements[j]))
            .collect();
        let input_2: Vec<Target> = (0..4)
            .map(|j| builder.select(path[i], h.elements[j], sibling.elements[j]))
            .collect();
        let new_h =
            builder.hash_n_to_hash_no_pad::<PoseidonHash>([input_1, input_2, vec![two]].concat());

        let h_targ: Vec<Target> = (0..4)
            .map(|j| builder.select(*selector, new_h.elements[j], h.elements[j]))
            .collect();
        h = HashOutTarget::from_vec(h_targ);
    }
    Ok(h)
}

// Note: this logic is in its own method for easy of reusability but
// specially to be able to test it isolated.
fn keypath_target<const MAX_DEPTH: usize>(
    builder: &mut CircuitBuilder<F, D>,
    key: &ValueTarget,
) -> Vec<BoolTarget> {
    let n_complete_field_elems: usize = MAX_DEPTH / F::BITS;
    let n_extra_bits: usize = MAX_DEPTH - n_complete_field_elems * F::BITS;

    let path: Vec<BoolTarget> = key
        .elements
        .iter()
        .take(n_complete_field_elems)
        .flat_map(|e| builder.split_le(*e, F::BITS))
        .collect();

    let extra_bits = if n_extra_bits > 0 {
        let extra_bits: Vec<BoolTarget> =
            builder.split_le(key.elements[n_complete_field_elems], F::BITS);
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
    key: &ValueTarget,
    value: &ValueTarget,
) -> HashOutTarget {
    let inputs = key
        .elements
        .iter()
        .chain(value.elements.iter())
        .cloned()
        .chain(iter::once(builder.one()))
        .collect();
    builder.hash_n_to_hash_no_pad::<PoseidonHash>(inputs)
}

#[cfg(test)]
pub mod tests {
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};
    use std::collections::HashMap;

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
            let key_targ = builder.add_virtual_value();
            let computed_path_targ = keypath_target::<MD>(&mut builder, &key_targ);
            for i in 0..MD {
                builder.connect(computed_path_targ[i].target, expected_path_targ[i].target);
            }

            // assign the input values to the targets
            pw.set_target_arr(&key_targ.elements, &key.0)?;
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
            let key_targ = builder.add_virtual_value();
            let value_targ = builder.add_virtual_value();

            let computed_h = kv_hash_target(&mut builder, &key_targ, &value_targ);
            builder.connect_hashes(computed_h, h_targ);

            // assign the input values to the targets
            pw.set_target_arr(&key_targ.elements, &key.0)?;
            pw.set_target_arr(&value_targ.elements, &value.0)?;
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
            (key, EMPTY_VALUE, tree.prove_nonexistence(&key)?)
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
    fn test_merkleproof_only_existence_verify() -> Result<()> {
        test_merkleproof_only_existence_verify_opt::<10>()?;
        test_merkleproof_only_existence_verify_opt::<16>()?;
        test_merkleproof_only_existence_verify_opt::<32>()?;
        test_merkleproof_only_existence_verify_opt::<40>()?;
        test_merkleproof_only_existence_verify_opt::<64>()?;
        test_merkleproof_only_existence_verify_opt::<128>()?;
        test_merkleproof_only_existence_verify_opt::<130>()?;
        test_merkleproof_only_existence_verify_opt::<250>()?;
        test_merkleproof_only_existence_verify_opt::<256>()?;
        Ok(())
    }

    fn test_merkleproof_only_existence_verify_opt<const MD: usize>() -> Result<()> {
        let mut kvs: HashMap<Value, Value> = HashMap::new();
        for i in 0..10 {
            kvs.insert(Value::from(hash_value(&Value::from(i))), Value::from(i));
        }

        let tree = MerkleTree::new(MD, &kvs)?;

        let key = Value::from(hash_value(&Value::from(5)));
        let (value, proof) = tree.prove(&key)?;
        assert_eq!(value, Value::from(5));
        assert_eq!(proof.existence, true);

        MerkleTree::verify(MD, tree.root(), &proof, &key, &value)?;

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofExistenceCircuit::<MD>::add_targets(&mut builder)?;
        targets.set_targets(&mut pw, tree.root(), proof, key, value)?;

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
            (EMPTY_VALUE, proof)
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

    #[test]
    fn test_wrong_witness() -> Result<()> {
        let mut kvs: HashMap<Value, Value> = HashMap::new();
        for i in 0..10 {
            kvs.insert(Value::from(i), Value::from(i));
        }
        const MD: usize = 16;
        let tree = MerkleTree::new(MD, &kvs)?;

        let key = Value::from(3);
        let (value, proof) = tree.prove(&key)?;

        // build another tree with an extra key-value, so that it has a
        // different root
        kvs.insert(Value::from(100), Value::from(100));
        let tree2 = MerkleTree::new(MD, &kvs)?;

        MerkleTree::verify(MD, tree.root(), &proof, &key, &value)?;
        assert_eq!(
            MerkleTree::verify(MD, tree2.root(), &proof, &key, &value)
                .unwrap_err()
                .to_string(),
            "proof of inclusion does not verify"
        );

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofCircuit::<MD>::add_targets(&mut builder)?;
        targets.set_targets(&mut pw, true, tree2.root(), proof, key, value)?;

        // generate proof, expecting it to fail (since we're using the wrong
        // root)
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err());

        Ok(())
    }
}
