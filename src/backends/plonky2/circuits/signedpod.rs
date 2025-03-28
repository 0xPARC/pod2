use anyhow::Result;
use itertools::Itertools;
use plonky2::{
    hash::hash_types::{HashOut, HashOutTarget},
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::circuit_builder::CircuitBuilder,
};

use crate::backends::plonky2::{
    basetypes::{Value, D, EMPTY_VALUE, F},
    circuits::common::{CircuitBuilderPod, StatementTarget, ValueTarget},
    primitives::{
        merkletree::{MerkleProof, MerkleProofExistenceGadget, MerkleProofExistenceTarget},
        signature::{PublicKey, SignatureVerifyGadget, SignatureVerifyTarget},
    },
    signedpod::SignedPod,
};
use crate::middleware::{hash_str, Params, PodType, KEY_SIGNER, KEY_TYPE};

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
        let value_type = builder.constant_value(Value::from(PodType::Signed));
        builder.connect_values(type_mt_proof.value, value_type);

        // 3.a. Verify signature
        let signature = SignatureVerifyGadget {}.eval(builder)?;

        // 3.b. Verify signer (ie. signature.pk == merkletree.signer_leaf)
        let signer_mt_proof = &mt_proofs[1];
        let key_signer = builder.constant_value(hash_str(KEY_SIGNER).into());
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
    pub fn pub_statements(&self) -> Vec<StatementTarget> {
        // TODO: Here we need to use the self.id in the ValueOf statements
        todo!()
    }

    pub fn set_targets(&self, pw: &mut PartialWitness<F>, pod: &SignedPod) -> Result<()> {
        // set the self.mt_proofs witness with the following order:
        // - KEY_TYPE leaf proof
        // - KEY_SIGNER leaf proof
        // - rest of leaves
        // - empty leaves (if needed)

        // add proof verification of KEY_TYPE & KEY_SIGNER leaves
        let key_type_key = Value::from(hash_str(KEY_TYPE));
        let key_signer_key = Value::from(hash_str(KEY_SIGNER));
        let key_signer_value = [key_type_key, key_signer_key]
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let (v, proof) = pod.dict.prove(&k)?;
                self.mt_proofs[i].set_targets(pw, true, pod.dict.commitment(), proof, *k, v)?;
                Ok(v)
            })
            .collect::<Result<Vec<Value>>>()?[1];

        // add the verification of the rest of leaves
        let mut curr = 2; // since we already added key_type and key_signer
        for (k, v) in pod.dict.iter().sorted_by_key(|kv| kv.0) {
            if *k == key_type_key || *k == key_signer_key {
                // skip the key_type & key_signer leaves, since they have
                // already been checked
                continue;
            }

            let (obtained_v, proof) = pod.dict.prove(&k)?;
            assert_eq!(obtained_v, *v); // sanity check

            self.mt_proofs[curr].set_targets(pw, true, pod.dict.commitment(), proof, *k, *v)?;
            curr += 1;
        }
        // sanity check
        assert!(curr <= self.params.max_signed_pod_values);

        // add the proofs of empty leaves (if needed), till the max_signed_pod_values
        for i in curr..self.params.max_signed_pod_values {
            self.mt_proofs[i].set_targets(
                pw,
                false, // disable verification
                pod.dict.commitment(),
                // use an empty proof:
                MerkleProof {
                    existence: true,
                    siblings: vec![],
                    other_leaf: None,
                },
                EMPTY_VALUE,
                EMPTY_VALUE,
            )?;
        }

        // get the signer pk
        let pk = PublicKey(key_signer_value);
        // the msg signed is the pod.id
        let msg = Value::from(pod.id.0);

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
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::backends::plonky2::{
        basetypes::C,
        primitives::signature::SecretKey,
        signedpod::{SignedPod, Signer},
    };
    use crate::middleware::F;

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let mut params = Params {
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
        let sk = SecretKey::new();
        let mut signer = Signer(sk);
        let pod = pod.sign(&mut signer).unwrap();
        let signed_pod = pod.pod.into_any().downcast::<SignedPod>().unwrap();

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
