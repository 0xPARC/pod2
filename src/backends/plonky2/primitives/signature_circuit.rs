#![allow(unused)]
use anyhow::Result;
use lazy_static::lazy_static;
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
    plonk::circuit_data::{
        CircuitConfig, CircuitData, ProverCircuitData, VerifierCircuitData, VerifierCircuitTarget,
    },
    plonk::config::Hasher,
    plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
};

use super::signature::{PublicKey, SecretKey, Signature, DUMMY_PUBLIC_INPUTS, DUMMY_SIGNATURE};
use crate::backends::plonky2::basetypes::{Hash, Proof, Value, C, D, EMPTY_HASH, EMPTY_VALUE, F};
use crate::backends::plonky2::circuits::common::{CircuitBuilderPod, ValueTarget};

lazy_static! {
    /// SignatureVerifyGadget VerifierCircuitData
    pub static ref S_VD: VerifierCircuitData<F,C,D> = SignatureVerifyGadget::verifier_data().unwrap();
}

pub struct SignatureVerifyGadget {}
pub struct SignatureTarget {
    // verifier_data of the SignatureInternalCircuit
    verifier_data_targ: VerifierCircuitTarget,
    selector: BoolTarget,
    pk: ValueTarget,
    // proof of the SignatureInternalCircuit (=signature::Signature.0)
    proof: ProofWithPublicInputsTarget<D>,
    dummy_proof: ProofWithPublicInputsTarget<D>,
}

impl SignatureVerifyGadget {
    pub fn verifier_data() -> Result<VerifierCircuitData<F, C, D>> {
        // notice that we use the 'zk' config
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let circuit = SignatureVerifyGadget {}.eval(&mut builder)?;

        let circuit_data = builder.build::<C>();
        Ok(circuit_data.verifier_data())
    }
}

impl SignatureVerifyGadget {
    /// creates the targets and defines the logic of the circuit
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignatureTarget> {
        let selector = builder.add_virtual_bool_target_safe();

        let common_data = super::signature::VP.0.common.clone();

        let pk_targ = builder.add_virtual_value();

        let verifier_data_targ =
            builder.add_virtual_verifier_data(common_data.config.fri_config.cap_height);

        let proof_targ = builder.add_virtual_proof_with_pis(&common_data);

        // NOTE: we would use the `conditional_verify_proof_or_dummy` method,
        // but since we're using the `standard_recursion_zk_config` (with zk),
        // internally it fails to generate the `dummy_circuit`, which mentions
        // that degree calculation could be off if zk is enabled. So we use
        // `conditional_verify_proof` feeding in our own dummy_proof
        // (signature::DUMMY_PROOF).
        let dummy_proof_targ = builder.add_virtual_proof_with_pis(&common_data);
        builder.conditionally_verify_proof::<C>(
            selector,
            &proof_targ,
            &verifier_data_targ,
            &dummy_proof_targ,
            &verifier_data_targ,
            &common_data,
        );

        Ok(SignatureTarget {
            selector,
            proof: proof_targ,
            pk: pk_targ,
            verifier_data_targ,
            dummy_proof: dummy_proof_targ,
        })
    }
}

impl SignatureTarget {
    /// assigns the given values to the targets
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        selector: bool,
        pk: PublicKey,
        msg: Value,
        signature: Signature,
    ) -> Result<()> {
        pw.set_bool_target(self.selector, selector)?;
        pw.set_target_arr(&self.pk.elements, &pk.0 .0)?;

        // note that this hash is checked again in-circuit at the `SignatureInternalCircuit`
        let s = Value(PoseidonHash::hash_no_pad(&[pk.0 .0, msg.0].concat()).elements);
        let public_inputs: Vec<F> = [pk.0 .0, msg.0, s.0].concat();

        pw.set_proof_with_pis_target(
            &self.proof,
            &ProofWithPublicInputs {
                proof: signature.0,
                public_inputs,
            },
        )?;

        pw.set_proof_with_pis_target(
            &self.dummy_proof,
            &ProofWithPublicInputs {
                proof: DUMMY_SIGNATURE.0.clone(),
                public_inputs: DUMMY_PUBLIC_INPUTS.clone(),
            },
        )?;

        pw.set_verifier_data_target(
            &self.verifier_data_targ,
            &super::signature::VP.0.verifier_only,
        )?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::backends::plonky2::basetypes::Hash;
    use crate::backends::plonky2::primitives::signature::SecretKey;

    use super::*;

    #[test]
    fn test_signature_gadget() -> Result<()> {
        // generate a valid signature
        let sk = SecretKey::new();
        let pk = sk.public_key();
        let msg = Value::from(42);
        let sig = sk.sign(msg)?;
        sig.verify(&pk, msg)?;

        // circuit
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
        targets.set_targets(&mut pw, true, pk, msg, sig)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        // verify the proof with the lazy_static loaded verifier_data (S_VD)
        S_VD.verify(ProofWithPublicInputs {
            proof: proof.proof.clone(),
            public_inputs: vec![],
        })?;

        Ok(())
    }

    #[test]
    fn test_signature_gadget_disabled() -> Result<()> {
        // generate a valid signature
        let sk = SecretKey::new();
        let pk = sk.public_key();
        let msg = Value::from(42);
        let sig = sk.sign(msg)?;
        // verification should pass
        sig.verify(&pk, msg)?;

        // replace the message, so that verifications should fail
        let msg = Value::from(24);
        // expect signature native verification to fail
        let v = sig.verify(&pk, Value::from(24));
        assert!(v.is_err(), "should fail to verify");

        // circuit
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();
        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
        targets.set_targets(&mut pw, true, pk.clone(), msg, sig.clone())?; // selector=true

        // generate proof, and expect it to fail
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err()); // expect prove to fail

        // build the circuit again, but now disable the selector that disables
        // the in-circuit signature verification
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
        targets.set_targets(&mut pw, false, pk, msg, sig)?; // selector=false

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        // verify the proof with the lazy_static loaded verifier_data (S_VD)
        S_VD.verify(ProofWithPublicInputs {
            proof: proof.proof.clone(),
            public_inputs: vec![],
        })?;

        Ok(())
    }
}
