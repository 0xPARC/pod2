//! Circuits compatible with the merkletree.rs implementation. This module
//! offers two different circuits:
//!
//! - `MerkleProofCircuit`: allows to verify both proofs of existence and proofs
//!   non-existence with the same circuit.
//! - `MerkleProofExistenceCircuit`: allows to verify proofs of existence only.
//!
//! If only proofs of existence are needed, use `MerkleProofExistenceCircuit`,
//! which requires less amount of constraints than `MerkleProofCircuit`.
//!
use std::iter;

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

use crate::{
    backends::plonky2::{
        basetypes::D,
        circuits::common::{CircuitBuilderPod, ValueTarget},
        primitives::merkletree::MerkleProof,
    },
    middleware::{Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE},
};

/// `MerkleProofGadget` allows to verify both proofs of existence and proofs
/// non-existence with the same circuit.
/// If only proofs of existence are needed, use `MerkleProofExistenceGadget`,
/// which requires less amount of constraints.
pub struct MerkleProofGadget {
    pub max_depth: usize,
}

#[derive(Clone)]
pub struct MerkleClaimAndProofTarget {
    pub(crate) max_depth: usize,
    // `enabled` determines if the merkleproof verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) root: HashOutTarget,
    pub(crate) key: ValueTarget,
    pub(crate) value: ValueTarget,
    pub(crate) existence: BoolTarget,
    pub(crate) siblings: Vec<HashOutTarget>,
    pub(crate) case_ii_selector: BoolTarget, // for case ii)
    pub(crate) other_key: ValueTarget,
    pub(crate) other_value: ValueTarget,
}

impl MerkleProofGadget {
    /// creates the targets and defines the logic of the circuit
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MerkleClaimAndProofTarget> {
        let enabled = builder.add_virtual_bool_target_safe();
        let root = builder.add_virtual_hash();
        let key = builder.add_virtual_value();
        let value = builder.add_virtual_value();
        // from proof struct:
        let existence = builder.add_virtual_bool_target_safe();
        // siblings are padded till max_depth length
        let siblings = builder.add_virtual_hashes(self.max_depth);

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
            (0..HASH_SIZE)
                .map(|j| builder.select(case_i_selector, empty_hash.elements[j], h.elements[j]))
                .collect(),
        );

        // get key's path
        let path = keypath_target(self.max_depth, builder, &key);

        // compute the root for the given siblings and the computed leaf_hash
        // (this is for the three cases (existence, non-existence case i, and
        // non-existence case ii).
        let obtained_root =
            compute_root_from_leaf(self.max_depth, builder, &path, &leaf_hash, &siblings)?;

        // check that obtained_root==root (from inputs), when enabled==true
        let zero = builder.zero();
        let expected_root: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(enabled, root.elements[j], zero))
            .collect();
        let computed_root: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(enabled, obtained_root.elements[j], zero))
            .collect();
        for j in 0..HASH_SIZE {
            builder.connect(computed_root[j], expected_root[j]);
        }

        Ok(MerkleClaimAndProofTarget {
            max_depth: self.max_depth,
            enabled,
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
}

impl MerkleClaimAndProofTarget {
    /// assigns the given values to the targets
    #[allow(clippy::too_many_arguments)]
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        // `enabled` determines if the merkleproof verification is enabled
        enabled: bool,
        existence: bool,
        root: Hash,
        proof: MerkleProof,
        key: RawValue,
        value: RawValue,
    ) -> Result<()> {
        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &key.0)?;
        pw.set_target_arr(&self.value.elements, &value.0)?;
        pw.set_bool_target(self.existence, existence)?;

        // pad siblings with zeros to length max_depth
        let mut siblings = proof.siblings.clone();
        siblings.resize(self.max_depth, EMPTY_HASH);
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
pub struct MerkleProofExistenceGadget {
    pub max_depth: usize,
}

pub struct MerkleProofExistenceTarget {
    max_depth: usize,
    // `enabled` determines if the merkleproof verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) root: HashOutTarget,
    pub(crate) key: ValueTarget,
    pub(crate) value: ValueTarget,
    pub(crate) siblings: Vec<HashOutTarget>,
}

impl MerkleProofExistenceGadget {
    /// creates the targets and defines the logic of the circuit
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<MerkleProofExistenceTarget> {
        let enabled = builder.add_virtual_bool_target_safe();
        let root = builder.add_virtual_hash();
        let key = builder.add_virtual_value();
        let value = builder.add_virtual_value();
        // siblings are padded till max_depth length
        let siblings = builder.add_virtual_hashes(self.max_depth);

        // get leaf's hash for the selected k & v
        let leaf_hash = kv_hash_target(builder, &key, &value);

        // get key's path
        let path = keypath_target(self.max_depth, builder, &key);

        // compute the root for the given siblings and the computed leaf_hash.
        let obtained_root =
            compute_root_from_leaf(self.max_depth, builder, &path, &leaf_hash, &siblings)?;

        // check that obtained_root==root (from inputs), when enabled==true
        let zero = builder.zero();
        let expected_root: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(enabled, root.elements[j], zero))
            .collect();
        let computed_root: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(enabled, obtained_root.elements[j], zero))
            .collect();
        for j in 0..HASH_SIZE {
            builder.connect(computed_root[j], expected_root[j]);
        }

        Ok(MerkleProofExistenceTarget {
            max_depth: self.max_depth,
            enabled,
            root,
            siblings,
            key,
            value,
        })
    }
}

impl MerkleProofExistenceTarget {
    /// assigns the given values to the targets
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        // `enabled` determines if the merkleproof verification is enabled
        enabled: bool,
        root: Hash,
        proof: MerkleProof,
        key: RawValue,
        value: RawValue,
    ) -> Result<()> {
        assert!(proof.existence); // sanity check

        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_hash_target(self.root, HashOut::from_vec(root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &key.0)?;
        pw.set_target_arr(&self.value.elements, &value.0)?;

        // pad siblings with zeros to length max_depth
        let mut siblings = proof.siblings.clone();
        siblings.resize(self.max_depth, EMPTY_HASH);
        assert_eq!(self.siblings.len(), siblings.len());

        for (i, sibling) in siblings.iter().enumerate() {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()))?;
        }

        Ok(())
    }
}

fn compute_root_from_leaf(
    max_depth: usize,
    builder: &mut CircuitBuilder<F, D>,
    path: &[BoolTarget],
    leaf_hash: &HashOutTarget,
    siblings: &[HashOutTarget],
) -> Result<HashOutTarget> {
    assert_eq!(siblings.len(), max_depth);
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

    let mut h = *leaf_hash;
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
        let input_1: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(path[i], sibling.elements[j], h.elements[j]))
            .collect();
        let input_2: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(path[i], h.elements[j], sibling.elements[j]))
            .collect();
        let new_h =
            builder.hash_n_to_hash_no_pad::<PoseidonHash>([input_1, input_2, vec![two]].concat());

        let h_targ: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(*selector, new_h.elements[j], h.elements[j]))
            .collect();
        h = HashOutTarget::from_vec(h_targ);
    }
    Ok(h)
}

// Note: this logic is in its own method for easy of reusability but
// specially to be able to test it isolated.
fn keypath_target(
    max_depth: usize,
    builder: &mut CircuitBuilder<F, D>,
    key: &ValueTarget,
) -> Vec<BoolTarget> {
    let n_complete_field_elems: usize = max_depth / F::BITS;
    let n_extra_bits: usize = max_depth - n_complete_field_elems * F::BITS;

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
    use std::collections::HashMap;

    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::{
        backends::plonky2::{basetypes::C, primitives::merkletree::*},
        middleware::{hash_value, RawValue},
    };

    #[test]
    fn test_keypath() -> Result<()> {
        for max_depth in [10, 16, 32, 40, 64, 128, 130, 250, 256] {
            test_keypath_opt(max_depth)?;
        }
        Ok(())
    }

    fn test_keypath_opt(max_depth: usize) -> Result<()> {
        for i in 0..5 {
            let config = CircuitConfig::standard_recursion_config();
            let mut builder = CircuitBuilder::<F, D>::new(config);
            let mut pw = PartialWitness::<F>::new();

            let key = RawValue::from(hash_value(&RawValue::from(i)));
            let expected_path = keypath(max_depth, key)?;

            // small circuit logic to check
            // expected_path_targ==keypath_target(key_targ)
            let expected_path_targ: Vec<BoolTarget> = (0..max_depth)
                .map(|_| builder.add_virtual_bool_target_safe())
                .collect();
            let key_targ = builder.add_virtual_value();
            let computed_path_targ = keypath_target(max_depth, &mut builder, &key_targ);
            for i in 0..max_depth {
                builder.connect(computed_path_targ[i].target, expected_path_targ[i].target);
            }

            // assign the input values to the targets
            pw.set_target_arr(&key_targ.elements, &key.0)?;
            for i in 0..max_depth {
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
            let key = RawValue::from(hash_value(&RawValue::from(i)));
            let value = RawValue::from(1000 + i);
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
        for max_depth in [10, 16, 32, 40, 64, 128, 130, 250, 256] {
            test_merkleproof_verify_opt(max_depth, true)?;
        }
        Ok(())
    }

    #[test]
    fn test_merkleproof_verify_nonexistence() -> Result<()> {
        for max_depth in [10, 16, 32, 40, 64, 128, 130, 250, 256] {
            test_merkleproof_verify_opt(max_depth, false)?;
        }
        Ok(())
    }

    // test logic to be reused both by the existence & nonexistence tests
    fn test_merkleproof_verify_opt(max_depth: usize, existence: bool) -> Result<()> {
        let mut kvs: HashMap<RawValue, RawValue> = HashMap::new();
        for i in 0..10 {
            kvs.insert(
                RawValue::from(hash_value(&RawValue::from(i))),
                RawValue::from(i),
            );
        }

        let tree = MerkleTree::new(max_depth, &kvs)?;

        let (key, value, proof) = if existence {
            let key = RawValue::from(hash_value(&RawValue::from(5)));
            let (value, proof) = tree.prove(&key)?;
            assert_eq!(value, RawValue::from(5));
            (key, value, proof)
        } else {
            let key = RawValue::from(hash_value(&RawValue::from(200)));
            (key, EMPTY_VALUE, tree.prove_nonexistence(&key)?)
        };
        assert_eq!(proof.existence, existence);

        if existence {
            MerkleTree::verify(max_depth, tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(max_depth, tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofGadget { max_depth }.eval(&mut builder)?;
        targets.set_targets(
            &mut pw,
            true, // verification enabled
            existence,
            tree.root(),
            proof,
            key,
            value,
        )?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_merkleproof_only_existence_verify() -> Result<()> {
        for max_depth in [10, 16, 32, 40, 64, 128, 130, 250, 256] {
            test_merkleproof_only_existence_verify_opt(max_depth)?;
        }
        Ok(())
    }

    fn test_merkleproof_only_existence_verify_opt(max_depth: usize) -> Result<()> {
        let mut kvs: HashMap<RawValue, RawValue> = HashMap::new();
        for i in 0..10 {
            kvs.insert(
                RawValue::from(hash_value(&RawValue::from(i))),
                RawValue::from(i),
            );
        }

        let tree = MerkleTree::new(max_depth, &kvs)?;

        let key = RawValue::from(hash_value(&RawValue::from(5)));
        let (value, proof) = tree.prove(&key)?;
        assert_eq!(value, RawValue::from(5));
        assert_eq!(proof.existence, true);

        MerkleTree::verify(max_depth, tree.root(), &proof, &key, &value)?;

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofExistenceGadget { max_depth }.eval(&mut builder)?;
        targets.set_targets(&mut pw, true, tree.root(), proof, key, value)?;

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
        kvs.insert(RawValue::from(0), RawValue::from(1000));
        kvs.insert(RawValue::from(2), RawValue::from(1002));
        kvs.insert(RawValue::from(5), RawValue::from(1005));
        kvs.insert(RawValue::from(13), RawValue::from(1013));

        let max_depth = 5;
        let tree = MerkleTree::new(max_depth, &kvs)?;
        // existence
        test_merkletree_edgecase_opt(max_depth, &tree, RawValue::from(5))?;
        // non-existence case i) expected leaf does not exist
        test_merkletree_edgecase_opt(max_depth, &tree, RawValue::from(1))?;
        // non-existence case ii) expected leaf does exist but it has a different 'key'
        test_merkletree_edgecase_opt(max_depth, &tree, RawValue::from(21))?;

        Ok(())
    }

    fn test_merkletree_edgecase_opt(
        max_depth: usize,
        tree: &MerkleTree,
        key: RawValue,
    ) -> Result<()> {
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
            MerkleTree::verify(max_depth, tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(max_depth, tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofGadget { max_depth }.eval(&mut builder)?;
        targets.set_targets(
            &mut pw,
            true, // verification enabled
            proof.existence,
            tree.root(),
            proof,
            key,
            value,
        )?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_wrong_witness() -> Result<()> {
        let mut kvs: HashMap<RawValue, RawValue> = HashMap::new();
        for i in 0..10 {
            kvs.insert(RawValue::from(i), RawValue::from(i));
        }
        let max_depth = 16;
        let tree = MerkleTree::new(max_depth, &kvs)?;

        let key = RawValue::from(3);
        let (value, proof) = tree.prove(&key)?;

        // build another tree with an extra key-value, so that it has a
        // different root
        kvs.insert(RawValue::from(100), RawValue::from(100));
        let tree2 = MerkleTree::new(max_depth, &kvs)?;

        MerkleTree::verify(max_depth, tree.root(), &proof, &key, &value)?;
        assert_eq!(
            MerkleTree::verify(max_depth, tree2.root(), &proof, &key, &value)
                .unwrap_err()
                .to_string(),
            "proof of inclusion does not verify"
        );

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofGadget { max_depth }.eval(&mut builder)?;
        targets.set_targets(
            &mut pw,
            true, // verification enabled
            true, // proof of existence
            tree2.root(),
            proof.clone(),
            key,
            value,
        )?;

        // generate proof, expecting it to fail (since we're using the wrong
        // root)
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err());

        // Now generate a new proof, using `enabled=false`, which should pass the verification
        // despite containing 'wrong' witness.
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleProofGadget { max_depth }.eval(&mut builder)?;
        targets.set_targets(
            &mut pw,
            false, // verification disabled
            true,  // proof of existence
            tree2.root(),
            proof,
            key,
            value,
        )?;

        // generate proof, should pass despite using wrong witness, since the
        // `enabled=false`
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
