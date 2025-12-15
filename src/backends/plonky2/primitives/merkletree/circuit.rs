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

use itertools::zip_eq;
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
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::D,
        circuits::common::{CircuitBuilderPod, ValueTarget},
        error::{Error, Result},
        primitives::merkletree::{
            MerkleClaimAndProof, MerkleTreeOp, MerkleTreeStateTransitionProof, TreeError,
        },
    },
    measure_gates_begin, measure_gates_end,
    middleware::{EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE},
};

#[derive(Clone, Debug, Serialize, Deserialize)]
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

/// Allows to verify both proofs of existence and proofs non-existence with the
/// same circuit. If only proofs of existence are needed, use
/// `verify_merkle_proof_existence_circuit`, which requires less amount of
/// constraints.
pub fn verify_merkle_proof_circuit(
    builder: &mut CircuitBuilder<F, D>,
    proof: &MerkleClaimAndProofTarget,
) {
    let max_depth = proof.max_depth;
    let measure = measure_gates_begin!(builder, format!("MerkleProof_{}", max_depth));

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
    let sum = builder.add(proof.existence.target, proof.case_ii_selector.target);
    // 2. sum * (sum-1) == 0
    builder.assert_bool(BoolTarget::new_unsafe(sum));

    // define the case_i_selector as true when both existence and
    // case_ii_selector are false:
    let not_existence = builder.not(proof.existence);
    let not_case_ii_selector = builder.not(proof.case_ii_selector);
    let case_i_selector = builder.and(not_existence, not_case_ii_selector);

    // use (key,value) or (other_key, other_value) depending if it's a proof
    // of existence or of non-existence, ie:
    // k = key * existence + other_key * (1-existence)
    // v = value * existence + other_value * (1-existence)
    let k = builder.select_value(proof.existence, proof.key, proof.other_key);
    let v = builder.select_value(proof.existence, proof.value, proof.other_value);

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
    let path = keypath_target(max_depth, builder, &proof.key);

    // compute the root for the given siblings and the computed leaf_hash
    // (this is for the three cases (existence, non-existence case i, and
    // non-existence case ii).
    let obtained_root =
        compute_root_from_leaf(max_depth, builder, &path, &leaf_hash, &proof.siblings);

    // check that obtained_root==root (from inputs), when enabled==true
    let zero = builder.zero();
    let expected_root: Vec<Target> = (0..HASH_SIZE)
        .map(|j| builder.select(proof.enabled, proof.root.elements[j], zero))
        .collect();
    let computed_root: Vec<Target> = (0..HASH_SIZE)
        .map(|j| builder.select(proof.enabled, obtained_root.elements[j], zero))
        .collect();
    for j in 0..HASH_SIZE {
        builder.connect(computed_root[j], expected_root[j]);
    }
    measure_gates_end!(builder, measure);
}

impl MerkleClaimAndProofTarget {
    pub fn new_virtual(max_depth: usize, builder: &mut CircuitBuilder<F, D>) -> Self {
        MerkleClaimAndProofTarget {
            max_depth,
            enabled: builder.add_virtual_bool_target_safe(),
            root: builder.add_virtual_hash(),
            key: builder.add_virtual_value(),
            value: builder.add_virtual_value(),
            // from proof struct:
            existence: builder.add_virtual_bool_target_safe(),
            // siblings are padded till max_depth length
            siblings: builder.add_virtual_hashes(max_depth),
            case_ii_selector: builder.add_virtual_bool_target_safe(),
            other_key: builder.add_virtual_value(),
            other_value: builder.add_virtual_value(),
        }
    }
    /// assigns the given values to the targets
    #[allow(clippy::too_many_arguments)]
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        enabled: bool,
        mp: &MerkleClaimAndProof,
    ) -> Result<()> {
        if mp.proof.siblings.len() > self.max_depth {
            return Err(Error::Tree(TreeError::circuit_depth_too_small(
                self.max_depth,
                mp.proof.siblings.len(),
            )));
        }

        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_hash_target(self.root, HashOut::from_vec(mp.root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &mp.key.0)?;
        pw.set_target_arr(&self.value.elements, &mp.value.0)?;
        pw.set_bool_target(self.existence, mp.proof.existence)?;

        // pad siblings with zeros to length max_depth
        for (i, sibling) in mp
            .proof
            .siblings
            .iter()
            .chain(iter::repeat(&EMPTY_HASH))
            .take(self.max_depth)
            .enumerate()
        {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()))?;
        }

        match mp.proof.other_leaf {
            Some((k, v)) if !mp.proof.existence => {
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

#[derive(Clone, Serialize, Deserialize)]
pub struct MerkleProofExistenceTarget {
    max_depth: usize,
    // `enabled` determines if the merkleproof verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) root: HashOutTarget,
    pub(crate) key: ValueTarget,
    pub(crate) value: ValueTarget,
    pub(crate) siblings: Vec<HashOutTarget>,
}

/// Allows to verify proofs of existence only. If proofs of non-existence are
/// needed, use `verify_merkle_proof_circuit`.
/// It returns the computed path, in case is needed at other parts of the upper
/// logic to avoid recomputing it again.
pub fn verify_merkle_proof_existence_circuit(
    builder: &mut CircuitBuilder<F, D>,
    proof: &MerkleProofExistenceTarget,
) -> Vec<BoolTarget> {
    let max_depth = proof.max_depth;
    let measure = measure_gates_begin!(builder, format!("MerkleProofExist_{}", max_depth));

    // get leaf's hash for the selected k & v
    let leaf_hash = kv_hash_target(builder, &proof.key, &proof.value);

    // get key's path
    let path = keypath_target(max_depth, builder, &proof.key);

    // compute the root for the given siblings and the computed leaf_hash.
    let obtained_root =
        compute_root_from_leaf(max_depth, builder, &path, &leaf_hash, &proof.siblings);

    // check that obtained_root==root (from inputs), when enabled==true
    let zero = builder.zero();
    let expected_root: Vec<Target> = (0..HASH_SIZE)
        .map(|j| builder.select(proof.enabled, proof.root.elements[j], zero))
        .collect();
    let computed_root: Vec<Target> = (0..HASH_SIZE)
        .map(|j| builder.select(proof.enabled, obtained_root.elements[j], zero))
        .collect();
    for j in 0..HASH_SIZE {
        builder.connect(computed_root[j], expected_root[j]);
    }
    measure_gates_end!(builder, measure);

    path
}

impl MerkleProofExistenceTarget {
    pub fn new_virtual(max_depth: usize, builder: &mut CircuitBuilder<F, D>) -> Self {
        MerkleProofExistenceTarget {
            max_depth,
            enabled: builder.add_virtual_bool_target_safe(),
            root: builder.add_virtual_hash(),
            key: builder.add_virtual_value(),
            value: builder.add_virtual_value(),
            // siblings are padded till max_depth length
            siblings: builder.add_virtual_hashes(max_depth),
        }
    }
    /// assigns the given values to the targets
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        enabled: bool,
        mp: &MerkleClaimAndProof,
    ) -> Result<()> {
        assert!(mp.proof.existence); // sanity check
        if mp.proof.siblings.len() > self.max_depth {
            return Err(Error::Tree(TreeError::circuit_depth_too_small(
                self.max_depth,
                mp.proof.siblings.len(),
            )));
        }

        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_hash_target(self.root, HashOut::from_vec(mp.root.0.to_vec()))?;
        pw.set_target_arr(&self.key.elements, &mp.key.0)?;
        pw.set_target_arr(&self.value.elements, &mp.value.0)?;

        // pad siblings with zeros to length max_depth
        for (i, sibling) in mp
            .proof
            .siblings
            .iter()
            .chain(iter::repeat(&EMPTY_HASH))
            .take(self.max_depth)
            .enumerate()
        {
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
) -> HashOutTarget {
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
    h
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

/// Verifies that the merkletree state transition (from old_root to new_root)
/// has been done correctly for the given new_key. This will allow verifying
/// correct new leaf insertion, and leaf edition&deletion (if needed).
/// See `MerkleTreeStateTransitionProof` struct for an explanation of the fields.
#[derive(Clone, Serialize, Deserialize)]
pub struct MerkleTreeStateTransitionProofTarget {
    pub(crate) max_depth: usize,
    // `enabled` determines if the merkleproof state transition verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) op: Target,
    pub(crate) old_root: HashOutTarget,
    pub(crate) op_proof: MerkleClaimAndProofTarget,
    pub(crate) new_root: HashOutTarget,
    pub(crate) op_key: ValueTarget,
    pub(crate) op_value: ValueTarget,
    pub(crate) siblings: Vec<HashOutTarget>,

    // auxiliary witness
    pub(crate) divergence_level: Target,
}
/// creates the targets and defines the logic of the circuit
pub fn verify_merkle_state_transition_circuit(
    builder: &mut CircuitBuilder<F, D>,
    proof: &MerkleTreeStateTransitionProofTarget,
) {
    let measure = measure_gates_begin!(
        builder,
        format!("MerkleProofStateTransition_{}", proof.max_depth)
    );
    let zero = builder.zero();
    let one = builder.one();
    let two = builder.constant(F::from_canonical_u64(2));

    // Op type check
    let is_insertion = builder.is_equal(proof.op, zero);
    let is_update = builder.is_equal(proof.op, one);
    let is_deletion = builder.is_equal(proof.op, two);
    let op_type_check = {
        let a = builder.or(is_insertion, is_update);
        builder.or(a, is_deletion)
    };
    builder.assert_one(op_type_check.target);

    // 1) Verify the provided op proof.
    verify_merkle_proof_circuit(builder, &proof.op_proof);

    // 2) Check that the provided siblings yield an existence proof of
    // (op_key, op_value) with root specified by op:
    // Insert: `new_root`
    // Update: `new_root`
    // Delete: `old_root`
    let root = HashOutTarget {
        elements: std::array::from_fn(|i| {
            builder.select(
                is_deletion,
                proof.old_root.elements[i],
                proof.new_root.elements[i],
            )
        }),
    };
    let new_key_proof = MerkleProofExistenceTarget {
        max_depth: proof.max_depth,
        enabled: proof.enabled,
        root,
        key: proof.op_key,
        value: proof.op_value,
        siblings: proof.siblings.clone(),
    };
    let new_leaf_path = verify_merkle_proof_existence_circuit(builder, &new_key_proof);

    // 3.1) assert that op_proof.existence is of the appropriate type according to op:
    // Insert/Delete: Non-existence
    // Update: Existence
    let proof_type = is_update;
    builder.conditional_assert_eq(
        proof.enabled.target,
        proof.op_proof.existence.target,
        proof_type.target,
    );
    // 3.2) assert that proof.enabled matches with op_proof.enabled
    builder.connect(proof.op_proof.enabled.target, proof.enabled.target);

    // 4) assert proof_non_existence.root corresponds to the root
    // specified by the op (old_root for Insert/Update and new_root
    // otherwise), and that it uses op_key
    let claim_root = HashOutTarget {
        elements: std::array::from_fn(|i| {
            builder.select(
                is_deletion,
                proof.new_root.elements[i],
                proof.old_root.elements[i],
            )
        }),
    };
    for j in 0..HASH_SIZE {
        // 4.1) assert that proof.proof_non_existence.root == proof.old_root
        builder.conditional_assert_eq(
            proof.enabled.target,
            proof.op_proof.root.elements[j],
            claim_root.elements[j],
        );
        // 4.2) assert that the non-existence proof uses the op_key (value not needed).
        builder.conditional_assert_eq(
            proof.enabled.target,
            proof.op_proof.key.elements[j],
            proof.op_key.elements[j],
        );
    }

    // prepare value for check 5.2)
    let old_leaf_hash = kv_hash_target(
        builder,
        &proof.op_proof.other_key,
        &proof.op_proof.other_value,
    );
    // prepare values for check 5.3)
    let old_leaf_path = keypath_target(proof.max_depth, builder, &proof.op_proof.other_key);

    // 5) check that old_siblings & new_siblings match as expected. They
    // should match at all levels for an update. Otherwise, let
    //    d=divergence_level and assert that:
    // 5.1) old_siblings[i] == new_siblings[i] ∀ i \ {d}
    // 5.2) at i==d, if old_siblings[i] != new_siblings[i]: old_siblings[i] ==
    //   EMPTY_HASH new_siblings[i] == old_leaf_hash
    // 5.3) assert that if old_key!=empty, both old_leaf_path&new_leaf_path
    //   should diverge at the inputted divergence level
    let old_siblings = proof.op_proof.siblings.clone();
    let new_siblings = proof.siblings.clone();
    for i in 0..proof.max_depth {
        let i_targ = builder.constant(F::from_canonical_u64(i as u64));
        let is_divergence_level = builder.is_equal(i_targ, proof.divergence_level);
        let is_not_update = builder.not(is_update);
        // There is no divergence level for an update.
        let is_divergence_level = builder.and(is_not_update, is_divergence_level);

        // 5.1) for all i except for i==divergence_level, assert that the
        //   siblings are the same
        let old_sibling_i: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(is_divergence_level, zero, old_siblings[i].elements[j]))
            .collect();
        let new_sibling_i: Vec<Target> = (0..HASH_SIZE)
            .map(|j| builder.select(is_divergence_level, zero, new_siblings[i].elements[j]))
            .collect();
        for j in 0..HASH_SIZE {
            builder.conditional_assert_eq(proof.enabled.target, old_sibling_i[j], new_sibling_i[j]);
        }

        // 5.2) when i==d && if old_siblings[i] != new_siblings[i], check that:
        //   old_siblings[i] == EMPTY_HASH && new_siblings[i] == old_leaf_hash

        // in_case_5_2=true if: i==d (= is_divergence_level) && old_siblings[i]!=new_siblings[i]
        let old_is_eq_new = zip_eq(old_siblings[i].elements, new_siblings[i].elements).fold(
            builder._true(),
            |acc, (old, new)| {
                let eq_at_i = builder.is_equal(old, new);
                builder.and(acc, eq_at_i)
            },
        );
        let old_is_noteq_new = builder.not(old_is_eq_new);
        let in_case_5_2 = builder.and(old_is_noteq_new, is_divergence_level);

        // do the case2's checks
        let sel = builder.and(proof.enabled, in_case_5_2);
        for j in 0..HASH_SIZE {
            builder.conditional_assert_eq(sel.target, old_siblings[i].elements[j], zero);
            builder.conditional_assert_eq(
                sel.target,
                new_siblings[i].elements[j],
                old_leaf_hash.elements[j],
            );
        }

        // 5.3) assert that if old_key!=empty, both old_leaf_path&new_leaf_path
        //   should diverge at the inputted divergence level. We can check it
        //   without having into account old_key!=empty, since if
        //   old_key==empty, the paths would still diverge.
        let paths_eq_at_d = builder.is_equal(old_leaf_path[i].target, new_leaf_path[i].target);
        builder.conditional_assert_eq(
            is_divergence_level.target,
            // expect them to not be equal, ie. the is_equal check to be 0
            paths_eq_at_d.target,
            zero,
        );
    }

    measure_gates_end!(builder, measure);
}

impl MerkleTreeStateTransitionProofTarget {
    pub fn new_virtual(max_depth: usize, builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            max_depth,
            enabled: builder.add_virtual_bool_target_safe(),
            op: builder.add_virtual_target(),

            old_root: builder.add_virtual_hash(),
            op_proof: MerkleClaimAndProofTarget::new_virtual(max_depth, builder),
            new_root: builder.add_virtual_hash(),
            op_key: builder.add_virtual_value(),
            op_value: builder.add_virtual_value(),
            // siblings are padded till max_depth length
            siblings: builder.add_virtual_hashes(max_depth),

            divergence_level: builder.add_virtual_target(),
        }
    }

    /// assigns the given values to the targets
    #[allow(clippy::too_many_arguments)]
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        enabled: bool,
        mp: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        let new_siblings = mp.siblings.clone();
        if new_siblings.len() > self.max_depth {
            return Err(Error::Tree(TreeError::circuit_depth_too_small(
                self.max_depth,
                new_siblings.len(),
            )));
        }

        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_target(self.op, F::from_canonical_u8(mp.op as u8))?;

        pw.set_hash_target(self.old_root, HashOut::from_vec(mp.old_root.0.to_vec()))?;
        self.op_proof.set_targets(
            pw,
            enabled,
            &MerkleClaimAndProof {
                root: if mp.op == MerkleTreeOp::Delete {
                    mp.new_root
                } else {
                    mp.old_root
                },
                key: mp.op_key,
                value: mp.value.unwrap_or(EMPTY_VALUE), // not needed for non-existence
                proof: mp.op_proof.clone(),
            },
        )?;

        pw.set_hash_target(self.new_root, HashOut::from_vec(mp.new_root.0.to_vec()))?;
        pw.set_target_arr(&self.op_key.elements, &mp.op_key.0)?;
        pw.set_target_arr(&self.op_value.elements, &mp.op_value.0)?;

        for (i, sibling) in new_siblings
            .iter()
            .chain(iter::repeat(&EMPTY_HASH))
            .take(self.max_depth)
            .enumerate()
        {
            pw.set_hash_target(self.siblings[i], HashOut::from_vec(sibling.0.to_vec()))?;
        }
        pw.set_target(
            self.divergence_level,
            F::from_canonical_u64((new_siblings.len() - 1) as u64),
        )?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;

    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            primitives::merkletree::{keypath, kv_hash, MerkleProof, MerkleTree},
        },
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
            let expected_path = keypath(key);

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
        crate::measure_gates_print!();
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

        let tree = MerkleTree::new(&kvs);

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
            MerkleTree::verify(tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleClaimAndProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_proof_circuit(&mut builder, &targets);
        targets.set_targets(
            &mut pw,
            true,
            &MerkleClaimAndProof::new(tree.root(), key, Some(value), proof),
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

        let tree = MerkleTree::new(&kvs);

        let key = RawValue::from(hash_value(&RawValue::from(5)));
        let (value, proof) = tree.prove(&key)?;
        assert_eq!(value, RawValue::from(5));
        assert!(proof.existence);

        MerkleTree::verify(tree.root(), &proof, &key, &value)?;

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleClaimAndProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_proof_circuit(&mut builder, &targets);
        targets.set_targets(
            &mut pw,
            true,
            &MerkleClaimAndProof::new(tree.root(), key, Some(value), proof),
        )?;

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
        let tree = MerkleTree::new(&kvs);
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
            MerkleTree::verify(tree.root(), &proof, &key, &value)?;
        } else {
            MerkleTree::verify_nonexistence(tree.root(), &proof, &key)?;
        }

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleClaimAndProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_proof_circuit(&mut builder, &targets);
        targets.set_targets(
            &mut pw,
            true,
            &MerkleClaimAndProof::new(tree.root(), key, Some(value), proof),
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
        let tree = MerkleTree::new(&kvs);

        let key = RawValue::from(3);
        let (value, proof) = tree.prove(&key)?;

        // build another tree with an extra key-value, so that it has a
        // different root
        kvs.insert(RawValue::from(100), RawValue::from(100));
        let tree2 = MerkleTree::new(&kvs);

        MerkleTree::verify(tree.root(), &proof, &key, &value)?;
        assert_eq!(
            MerkleTree::verify(tree2.root(), &proof, &key, &value)
                .unwrap_err()
                .inner()
                .unwrap()
                .to_string(),
            "proof of inclusion does not verify"
        );

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleClaimAndProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_proof_circuit(&mut builder, &targets);
        // verification enabled & proof of existence
        let mp = MerkleClaimAndProof::new(tree2.root(), key, Some(value), proof);
        targets.set_targets(&mut pw, true, &mp)?;

        // generate proof, expecting it to fail (since we're using the wrong
        // root)
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err());

        // Now generate a new proof, using `enabled=false`, which should pass the verification
        // despite containing 'wrong' witness.
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleClaimAndProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_proof_circuit(&mut builder, &targets);
        // verification disabled & proof of existence
        targets.set_targets(&mut pw, false, &mp)?;

        // generate proof, should pass despite using wrong witness, since the
        // `enabled=false`
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }

    fn run_state_transition_circuit(
        expect_pass: bool,
        max_depth: usize,
        state_transition_proof: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        // sanity check, run the out-circuit proof verification
        if expect_pass {
            MerkleTree::verify_state_transition(state_transition_proof)?;
        } else {
            // expect out-circuit verification to fail
            let _ = MerkleTree::verify_state_transition(state_transition_proof).is_err();
        }

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleTreeStateTransitionProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_state_transition_circuit(&mut builder, &targets);
        targets.set_targets(&mut pw, true, state_transition_proof)?;

        // generate & verify proof
        let data = builder.build::<C>();
        if expect_pass {
            let proof = data.prove(pw)?;
            data.verify(proof)?;
        } else {
            assert!(data.prove(pw).is_err()); // expect prove to fail
        }
        Ok(())
    }

    #[test]
    fn test_state_transition_gadget() -> Result<()> {
        let max_depth: usize = 32;
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }
        let mut tree = MerkleTree::new(&kvs);

        // key=37 shares path with key=5, till the level 6, needing 2 extra
        // 'empty' nodes between the original position of key=5 with the new
        // position of key=5 and key=37.
        let old_root = tree.root();
        let key = RawValue::from(37);
        let value = RawValue::from(1037);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // Deleting this key should yield the old tree, and the proof
        // should be the same (mutatis mutandis).
        let mut tree_with_deleted_key = tree.clone();
        let state_transition_proof1 = tree_with_deleted_key.delete(&key)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof1)?;
        assert_eq!(state_transition_proof1.old_root, tree.root());
        assert_eq!(state_transition_proof1.new_root, old_root);

        // add a new leaf, which shares path with the previous one, but diverges
        // one level before, where there is no leaf yet to be pushed down.
        let mut tree_with_another_leaf = tree.clone();
        let old_root = tree_with_another_leaf.root();
        let key = RawValue::from(21);
        let value = RawValue::from(1021);
        let state_transition_proof = tree_with_another_leaf.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(
            state_transition_proof.new_root,
            tree_with_another_leaf.root()
        );

        // Alternatively add this key with another value then update.
        let value1 = RawValue::from(99);
        tree.insert(&key, &value1)?;
        let state_transition_proof1 = tree.update(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof1)?;
        assert_eq!(tree.root(), tree_with_another_leaf.root());

        // another leaf which will push further down the leaf with key=37
        let old_root = tree.root();
        let key = RawValue::from(101);
        let value = RawValue::from(1101);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // insert two more leaves, which share almost all the path except for
        // the last level (max_depth-1)

        let max_depth: usize = 32;
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }
        let mut tree = MerkleTree::new(&kvs);

        let old_root = tree.root();
        let key = RawValue::from(4294967295); // 0xffffffff
        let value = RawValue::from(4294967295);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // insert a leaf that shares the path with the previous one, except for
        // the last level (in max_depth); which would force both leaves to be
        // pushed down till max_depth-1 level.
        let old_root = tree.root();
        let key = RawValue::from(4026531839); // 0xefffffff
        let value = RawValue::from(4026531839);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // ...and delete.
        let state_transition_proof1 = tree.delete(&key)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof1)?;
        assert_eq!(
            state_transition_proof1.old_root,
            state_transition_proof.new_root
        );
        assert_eq!(
            state_transition_proof1.new_root,
            state_transition_proof.old_root
        );

        // ...and add a key-value pair with the same key but a
        // different value, then update.
        let value1 = RawValue::from(50);
        let state_transition_proof1 = tree.insert(&key, &value1)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof1)?;
        assert_eq!(
            state_transition_proof1.old_root,
            state_transition_proof.old_root
        );

        let state_transition_proof2 = tree.update(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof2)?;
        assert_eq!(
            state_transition_proof2.old_root,
            state_transition_proof1.new_root
        );
        assert_eq!(
            state_transition_proof2.new_root,
            state_transition_proof.new_root
        );

        Ok(())
    }

    #[test]
    fn test_state_transition_gadget_with_alteration() -> Result<()> {
        let max_depth: usize = 32;
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }
        let mut tree = MerkleTree::new(&kvs);

        // key=37 shares path with key=5, till the level 6, needing 2 extra
        // 'empty' nodes between the original position of key=5 with the new
        // position of key=5 and key=37.
        let old_root = tree.root();
        let key = RawValue::from(37);
        let value = RawValue::from(1037);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // add a new leaf, which shares path with the previous one, but diverges
        // one level before, where there is no leaf yet to be pushed down.
        let old_root = tree.root();
        let key = RawValue::from(21);
        let value = RawValue::from(1021);
        let state_transition_proof = tree.insert(&key, &value)?;
        run_state_transition_circuit(true, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_eq!(state_transition_proof.new_root, tree.root());

        // another leaf which will push further down the leaf with key=37
        let old_root = tree.root();
        let key = RawValue::from(101);
        let value = RawValue::from(1101);
        let mut state_transition_proof = tree.insert(&key, &value)?;

        // Tamper with state transition.
        const OFFSET: usize = 20;
        let other_leaf = state_transition_proof.op_proof.other_leaf.unwrap();
        let altered_proof = MerkleProof {
            existence: true,
            siblings: [
                state_transition_proof.op_proof.siblings.clone(),
                vec![EMPTY_HASH; OFFSET],
                vec![kv_hash(&other_leaf.0, Some(other_leaf.1))],
            ]
            .concat(),
            other_leaf: None,
        };
        let altered_root = altered_proof.compute_root_from_leaf(
            &state_transition_proof.op_key,
            Some(state_transition_proof.op_value),
        )?;
        state_transition_proof.siblings = altered_proof.siblings;
        state_transition_proof.new_root = altered_root;

        run_state_transition_circuit(false, max_depth, &state_transition_proof)?;
        assert_eq!(state_transition_proof.old_root, old_root);
        assert_ne!(state_transition_proof.new_root, tree.root()); // Tamper check
        Ok(())
    }

    #[test]
    fn test_state_transition_gadget_disabled() -> Result<()> {
        let max_depth: usize = 32;
        let mut kvs = HashMap::new();
        for i in 0..8 {
            kvs.insert(RawValue::from(i), RawValue::from(1000 + i));
        }
        let mut tree = MerkleTree::new(&kvs);

        let key = RawValue::from(37);
        let value = RawValue::from(1037);
        let _ = tree.insert(&key, &value)?;

        let key = RawValue::from(21);
        let value = RawValue::from(1021);
        let original_state_transition_proof = tree.insert(&key, &value)?;

        let mut state_transition_proof = original_state_transition_proof.clone();

        // modify the proof, so that it should fail when `enabled=true`, by
        // changing the new_root
        state_transition_proof.new_root = state_transition_proof.old_root;

        run_circuit_disabled(max_depth, &state_transition_proof)?;

        // modify the proof, so that it should fail when `enabled=true`, by
        // changing the new_sibling at the divergence level, which should not
        // pass the verification in the case where we're inserting key=21
        let mut state_transition_proof = original_state_transition_proof.clone();
        state_transition_proof.siblings[4] = EMPTY_HASH;

        run_circuit_disabled(max_depth, &state_transition_proof)?;

        Ok(())
    }

    fn run_circuit_disabled(
        max_depth: usize,
        state_transition_proof: &MerkleTreeStateTransitionProof,
    ) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleTreeStateTransitionProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_state_transition_circuit(&mut builder, &targets);
        targets.set_targets(&mut pw, true, state_transition_proof)?;

        // generate proof, and expect it to fail
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err()); // expect prove to fail

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = MerkleTreeStateTransitionProofTarget::new_virtual(max_depth, &mut builder);
        verify_merkle_state_transition_circuit(&mut builder, &targets);
        targets.set_targets(&mut pw, false, state_transition_proof)?;

        // generate and expect it to pass
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }
}
