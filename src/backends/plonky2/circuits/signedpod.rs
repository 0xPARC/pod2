use anyhow::Result;
use itertools::Itertools;
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
use std::collections::HashMap;
use std::iter;

use crate::backends::plonky2::basetypes::{Hash, Value, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE};
use crate::backends::plonky2::circuits::common::{
    CircuitBuilderPod, OperationTarget, StatementTarget, ValueTarget,
};
use crate::backends::plonky2::primitives::merkletree::MerkleTree;
use crate::backends::plonky2::primitives::merkletree::{
    MerkleProofExistenceGadget, MerkleProofExistenceTarget,
};
use crate::middleware::{
    hash_str, AnchoredKey, NativeOperation, NativePredicate, Params, PodType, Statement,
    StatementArg, ToFields, KEY_TYPE, SELF,
};

use super::common::Flattenable;

pub struct SignedPodVerifyGadget {
    pub params: Params,
}

impl SignedPodVerifyGadget {
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignedPodVerifyTarget> {
        // 2. Verify id
        let id = builder.add_virtual_hash();
        let mut mt_proofs = Vec::new();
        for _ in 0..self.params.max_signed_pod_values {
            let mt_proof = MerkleProofExistenceGadget {
                max_depth: self.params.max_depth_mt_gadget,
            }
            .eval(builder)?;
            builder.connect_hashes(id, mt_proof.root);
            mt_proofs.push(mt_proof);
        }

        // 1. Verify type
        let type_mt_proof = &mt_proofs[0];
        let key_type = builder.constant_value(hash_str(KEY_TYPE).into());
        builder.connect_values(type_mt_proof.key, key_type);
        let value_type = builder.constant_value(Value::from(PodType::MockSigned));
        builder.connect_values(type_mt_proof.value, value_type);

        // 3. TODO: Verify signature

        Ok(SignedPodVerifyTarget {
            params: self.params.clone(),
            id,
            mt_proofs,
        })
    }
}

pub struct SignedPodVerifyTarget {
    params: Params,
    id: HashOutTarget,
    // The KEY_TYPE entry must be the first one
    // The KEY_SIGNER entry must be the second one
    mt_proofs: Vec<MerkleProofExistenceTarget>,
}

pub struct SignedPodVerifyInput {
    pub kvs: HashMap<Value, Value>,
}

impl SignedPodVerifyTarget {
    fn kvs(&self) -> Vec<(ValueTarget, ValueTarget)> {
        let mut kvs = Vec::new();
        for mt_proof in &self.mt_proofs {
            kvs.push((mt_proof.key, mt_proof.value));
        }
        // TODO: when the slot is unused, do we force the kv to be (EMPTY, EMPTY), and then from
        // it get a ValueOf((id, EMPTY), EMPTY)?  Or should we keep some boolean flags for unused
        // slots and translate them to Statement::None instead?
        kvs
    }

    pub fn pub_statements(&self) -> Vec<StatementTarget> {
        // TODO: Here we need to use the self.id in the ValueOf statements
        todo!()
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        input: &SignedPodVerifyInput,
    ) -> Result<()> {
        assert!(input.kvs.len() <= self.params.max_signed_pod_values);
        let tree = MerkleTree::new(self.params.max_depth_mt_gadget, &input.kvs)?;

        // First handle the type entry, then the rest of the entries, and finally pad with
        // repetitions of the type entry (which always exists)
        let mut kvs = input.kvs.clone();
        let key_type = Value::from(hash_str(KEY_TYPE));
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");

        // TODO manage unused merkleproof verifications (with selectors)
        for (i, (k, v)) in iter::once((key_type, value_type))
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0))
            .chain(iter::repeat((key_type, value_type)))
            .take(self.params.max_signed_pod_values)
            .enumerate()
        {
            let (_, proof) = tree.prove(&k)?;
            self.mt_proofs[i].set_targets(pw, true, tree.root(), proof, k, v)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backends::plonky2::mock::mainpod;
    use crate::backends::plonky2::{basetypes::C, mock::mainpod::OperationArg};
    use crate::middleware::{OperationType, PodId};
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let params = Params::default();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let signed_pod_verify = SignedPodVerifyGadget { params }.eval(&mut builder)?;

        let mut pw = PartialWitness::<F>::new();
        let kvs = [
            (
                Value::from(hash_str(KEY_TYPE)),
                Value::from(PodType::MockSigned),
            ),
            (Value::from(hash_str("foo")), Value::from(42)),
        ]
        .into();
        let input = SignedPodVerifyInput { kvs };
        signed_pod_verify.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
