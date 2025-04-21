use std::iter;

use anyhow::Result;
use itertools::Itertools;
use plonky2::{
    hash::hash_types::{HashOut, HashOutTarget},
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::{
    backends::plonky2::{
        basetypes::D,
        circuits::common::{CircuitBuilderPod, StatementArgTarget, StatementTarget, ValueTarget},
        primitives::{
            merkletree::{
                MerkleClaimAndProof, MerkleProofExistenceGadget, MerkleProofExistenceTarget,
            },
            signature::{PublicKey, SignatureVerifyGadget, SignatureVerifyTarget},
        },
        signedpod::SignedPod,
    },
    middleware::{
        hash_str, Key, NativePredicate, Params, PodType, Predicate, RawValue, ToFields, Value, F,
        KEY_SIGNER, KEY_TYPE, SELF,
    },
};

pub struct SignedPodVerifyGadget {
    pub params: Params,
}

impl SignedPodVerifyGadget {
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignedPodVerifyTarget> {
        // 1. Verify id
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

        // 2. Verify type
        let type_mt_proof = &mt_proofs[0];
        let key_type = builder.constant_value(hash_str(KEY_TYPE).into());
        builder.connect_values(type_mt_proof.key, key_type);
        let value_type = builder.constant_value(Value::from(PodType::Signed).raw());
        builder.connect_values(type_mt_proof.value, value_type);

        // 3.a. Verify signature
        let signature = SignatureVerifyGadget {}.eval(builder)?;

        // 3.b. Verify signer (ie. signature.pk == merkletree.signer_leaf)
        let signer_mt_proof = &mt_proofs[1];
        let key_signer = builder.constant_value(Key::from(KEY_SIGNER).raw());
        builder.connect_values(signer_mt_proof.key, key_signer);
        builder.connect_values(signer_mt_proof.value, signature.pk);

        // 3.c. connect signed message to pod.id
        builder.connect_values(ValueTarget::from_slice(&id.elements), signature.msg);

        Ok(SignedPodVerifyTarget {
            params: self.params.clone(),
            id,
            mt_proofs,
            signature,
        })
    }
}

pub struct SignedPodVerifyTarget {
    params: Params,
    id: HashOutTarget,
    // the KEY_TYPE entry must be the first one
    // the KEY_SIGNER entry must be the second one
    mt_proofs: Vec<MerkleProofExistenceTarget>,
    signature: SignatureVerifyTarget,
}

impl SignedPodVerifyTarget {
    pub fn pub_statements(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        self_id: bool,
    ) -> Vec<StatementTarget> {
        let mut statements = Vec::new();
        let predicate: [Target; Params::predicate_size()] = builder
            .constants(&Predicate::Native(NativePredicate::ValueOf).to_fields(&self.params))
            .try_into()
            .expect("size predicate_size");
        let pod_id = if self_id {
            builder.constant_value(SELF.0.into())
        } else {
            ValueTarget {
                elements: self.id.elements,
            }
        };
        for mt_proof in &self.mt_proofs {
            let args = [
                StatementArgTarget::anchored_key(builder, &pod_id, &mt_proof.key),
                StatementArgTarget::literal(builder, &mt_proof.value),
            ]
            .into_iter()
            .chain(iter::repeat_with(|| StatementArgTarget::none(builder)))
            .take(self.params.max_statement_args)
            .collect();
            let statement = StatementTarget { predicate, args };
            statements.push(statement);
        }
        statements
    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, pod: &SignedPod) -> Result<()> {
        // set the self.mt_proofs witness with the following order:
        // - KEY_TYPE leaf proof
        // - KEY_SIGNER leaf proof
        // - rest of leaves
        // - empty leaves (if needed)

        // add proof verification of KEY_TYPE & KEY_SIGNER leaves
        let key_type_key = Key::from(KEY_TYPE);
        let key_signer_key = Key::from(KEY_SIGNER);
        let key_signer_value = [&key_type_key, &key_signer_key]
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let (v, proof) = pod.dict.prove(k)?;
                self.mt_proofs[i].set_targets(
                    pw,
                    true,
                    &MerkleClaimAndProof::new(pod.dict.commitment(), k.raw(), Some(v.raw()), proof),
                )?;
                Ok(v)
            })
            .collect::<Result<Vec<&Value>>>()?[1];

        // add the verification of the rest of leaves
        let mut curr = 2; // since we already added key_type and key_signer
        for (k, v) in pod.dict.kvs().iter().sorted_by_key(|kv| kv.0.hash()) {
            if *k == key_type_key || *k == key_signer_key {
                // skip the key_type & key_signer leaves, since they have
                // already been checked
                continue;
            }

            let (obtained_v, proof) = pod.dict.prove(k)?;
            assert_eq!(obtained_v, v); // sanity check

            self.mt_proofs[curr].set_targets(
                pw,
                true,
                &MerkleClaimAndProof::new(pod.dict.commitment(), k.raw(), Some(v.raw()), proof),
            )?;
            curr += 1;
        }
        // sanity check
        assert!(curr <= self.params.max_signed_pod_values);

        // add the proofs of empty leaves (if needed), till the max_signed_pod_values
        let mut mp = MerkleClaimAndProof::empty();
        mp.root = pod.dict.commitment();
        for i in curr..self.params.max_signed_pod_values {
            self.mt_proofs[i].set_targets(pw, false, &mp)?;
        }

        // get the signer pk
        let pk = PublicKey(key_signer_value.raw());
        // the msg signed is the pod.id
        let msg = RawValue::from(pod.id.0);

        // set signature targets values
        self.signature
            .set_targets(pw, true, pk, msg, pod.signature.clone())?;

        // set the id target value
        pw.set_hash_target(self.id, HashOut::from_vec(pod.id.0 .0.to_vec()))?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            primitives::signature::SecretKey,
            signedpod::{SignedPod, Signer},
        },
        middleware::F,
    };

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let params = Params {
            max_signed_pod_values: 6,
            ..Default::default()
        };
        // set max_signed_pod_values to 6, and we insert 3 leaves, so that the
        // circuit has enough space for the 3 leaves plus the KEY_TYPE and
        // KEY_SIGNER and one empty leaf.

        // prepare a signedpod
        let mut pod = crate::frontend::SignedPodBuilder::new(&params);
        pod.insert("idNumber", "4242424242");
        pod.insert("dateOfBirth", 1169909384);
        pod.insert("socialSecurityNumber", "G2121210");
        let sk = SecretKey::new_rand();
        let mut signer = Signer(sk);
        let pod = pod.sign(&mut signer).unwrap();
        let signed_pod = (pod.pod as Box<dyn Any>).downcast::<SignedPod>().unwrap();

        // use the pod in the circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        // build the circuit logic
        let signed_pod_verify = SignedPodVerifyGadget { params }.eval(&mut builder)?;

        // set the signed_pod as target values for the circuit
        signed_pod_verify.set_targets(&mut pw, &signed_pod)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;

        Ok(())
    }
}
