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

// TODO TMP
const MAX_DEPTH: usize = 256;

pub struct MerkleProofCircuit {
    existence_targ: BoolTarget,
    siblings_targ: Vec<HashOutTarget>,
    leaf: (Vec<Target>, Vec<Target>),
    other_leaf: (Vec<Target>, Vec<Target>),
}
impl MerkleProofCircuit {
    /// creates the targets and defines the logic of the circuit
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        // create the targets
        let existence_targ = builder.add_virtual_bool_target_safe();
        let siblings_targ = builder.add_virtual_targets(HASH_SIZE * MAX_DEPTH);
        let key = builder.add_virtual_targets(VALUE_SIZE);
        let value = builder.add_virtual_targets(VALUE_SIZE);
        let other_key = builder.add_virtual_targets(VALUE_SIZE);
        let other_value = builder.add_virtual_targets(VALUE_SIZE);

        // get key's path
        let path: Vec<BoolTarget> = key
            .iter()
            .flat_map(|e| builder.split_le(*e, MAX_DEPTH / 4))
            .collect();
        todo!();
    }

    /// assigns the given values to the targets
    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        existence: bool,
        siblings: Vec<Hash>,
        other_leaf: (Value, Value),
        s: Value,
    ) -> Result<()> {
        todo!();
    }
}

// Note: this logic is in its own method for easy of reusability but specially
// to be able to test it isolated
fn keypath_target(builder: &mut CircuitBuilder<F, D>, key: &Vec<Target>) -> Vec<BoolTarget> {
    assert_eq!(key.len(), VALUE_SIZE);
    key.iter()
        .flat_map(|e| builder.split_le(*e, F::BITS))
        .collect()
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
        for i in 0..100 {
            let key = Value::from(hash_value(&Value::from(100 + i)));
            let path = keypath(MAX_DEPTH, key)?;
            test_keypath_opt(key, path)?;
        }
        Ok(())
    }
    fn test_keypath_opt(key: Value, expected_path: Vec<bool>) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

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
        let mut pw = PartialWitness::<F>::new();
        pw.set_target_arr(&key_targ, &key.0.to_vec())?;
        for i in 0..MAX_DEPTH {
            pw.set_bool_target(expected_path_targ[i], expected_path[i])?;
        }

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
