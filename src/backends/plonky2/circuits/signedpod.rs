use anyhow::Result;
use plonky2::{
    hash::hash_types::{HashOut, HashOutTarget},
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::circuit_builder::CircuitBuilder,
};

use crate::backends::plonky2::basetypes::{Value, D, EMPTY_VALUE, F};
use crate::backends::plonky2::circuits::common::{CircuitBuilderPod, StatementTarget};
use crate::backends::plonky2::primitives::{
    merkletree::{MerkleProof, MerkleProofExistenceGadget, MerkleProofExistenceTarget},
    signature::{PublicKey, SignatureVerifyGadget, SignatureVerifyTarget},
};
use crate::backends::plonky2::signedpod::SignedPod;
use crate::middleware::{hash_str, Params, PodType, KEY_SIGNER, KEY_TYPE};

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
        let value_type = builder.constant_value(Value::from(PodType::Signed));
        builder.connect_values(type_mt_proof.value, value_type);

        // 3. Verify signature
        let signature = SignatureVerifyGadget {}.eval(builder)?;

        // 4. Verify signer (ie. signature.pk == merkletree.signer_leaf
        let signer_mt_proof = &mt_proofs[1];
        let key_signer = builder.constant_value(hash_str(KEY_SIGNER).into());
        builder.connect_values(signer_mt_proof.key, key_signer);
        builder.connect_values(signer_mt_proof.value, signature.pk);

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
    // pub fn kvs(&self) -> Vec<(ValueTarget, ValueTarget)> { // UNUSED?
    //     let mut kvs = Vec::new();
    //     for mt_proof in &self.mt_proofs {
    //         kvs.push((mt_proof.key, mt_proof.value));
    //     }
    //     // TODO: when the slot is unused, do we force the kv to be (EMPTY, EMPTY), and then from
    //     // it get a ValueOf((id, EMPTY), EMPTY)?  Or should we keep some boolean flags for unused
    //     // slots and translate them to Statement::None instead?
    //     kvs
    // }

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
        let key_type_key = Value::from(hash_str(KEY_TYPE));
        let key_signer_key = Value::from(hash_str(KEY_SIGNER));
        let (key_type_value, proof) = pod.dict.prove(&key_type_key)?;
        self.mt_proofs[0].set_targets(
            pw,
            true,
            pod.dict.commitment(),
            proof,
            key_type_key,
            key_type_value,
        )?;
        let (key_signer_value, proof) = pod.dict.prove(&key_signer_key)?;
        self.mt_proofs[1].set_targets(
            pw,
            true,
            pod.dict.commitment(),
            proof,
            key_signer_key,
            key_signer_value,
        )?;

        // add the rest of leaves
        let mut curr = 2; // since we already added key_type and key_signer
        for (k, v) in pod.dict.iter() {
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

        // add the empty leaves (if needed)
        for i in curr..self.params.max_signed_pod_values {
            let empty_proof = MerkleProof {
                existence: true,
                siblings: vec![],
                other_leaf: None,
            };
            self.mt_proofs[i].set_targets(
                pw,
                false, // disable verification
                pod.dict.commitment(),
                empty_proof,
                EMPTY_VALUE,
                EMPTY_VALUE,
            )?;
        }

        // get the signer pk
        // let pk = PublicKey(pod.dict.get(&Value::from(hash_str(KEY_SIGNER)))?);
        let pk = PublicKey(key_signer_value);
        // the msg signed is the pod.id
        let msg = Value::from(pod.id.0);

        // set signature targets values
        self.signature
            .set_targets(pw, true, pk, msg, pod.signature.clone())?; // selector=false

        // set the id target value
        pw.set_hash_target(self.id, HashOut::from_vec(pod.id.0 .0.to_vec()))?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::backends::plonky2::basetypes::C;
    use crate::backends::plonky2::primitives::signature::SecretKey;
    use crate::backends::plonky2::signedpod::{SignedPod, Signer};
    use crate::middleware::F;

    #[test]
    fn test_signed_pod_verify() -> Result<()> {
        let mut params = Params::default();
        // set max_signed_pod_values to 6, and we insert 3 leaves, so that the
        // circuit has enough space for the 3 leaves plus the KEY_TYPE and
        // KEY_SIGNER and one empty leave.
        params.max_signed_pod_values = 6;

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
