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

use crate::backends::plonky2::basetypes::{Hash, Value, C, D, EMPTY_HASH, EMPTY_VALUE, F};
use crate::backends::plonky2::circuits::common::{CircuitBuilderPod, ValueTarget};
use crate::backends::plonky2::primitives::signature::{PublicKey, Signature};

lazy_static! {
    // SignatureGate VerifierCircuitData
    pub static ref S_VD: VerifierCircuitData<F,C,D> = SignatureGate::verifier_data().unwrap();
}

pub struct SignatureGate {}
pub struct SignatureTarget {
    // verifier_data of the SignatureInternalCircuit
    verifier_data_targ: VerifierCircuitTarget,
    selector: BoolTarget,
    pk: ValueTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

impl SignatureGate {
    pub fn verifier_data() -> Result<VerifierCircuitData<F, C, D>> {
        // notice that we use the 'zk' config
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let circuit = SignatureGate {}.eval(&mut builder)?;

        let circuit_data = builder.build::<C>();
        Ok(circuit_data.verifier_data())
    }
}

impl SignatureGate {
    /// creates the targets and defines the logic of the circuit
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignatureTarget> {
        let selector = builder.add_virtual_bool_target_safe();

        let common_data = super::signature::VP.0.common.clone();

        let pk_targ = builder.add_virtual_value();

        let verifier_data_targ =
            builder.add_virtual_verifier_data(common_data.config.fri_config.cap_height);

        let proof_targ = builder.add_virtual_proof_with_pis(&common_data);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &common_data);
        // NOTE: we would use the `conditional_verify...` method, but since we're using the
        // `standard_recursion_zk_config` (with zk), internally it fails to generate the
        // `dummy_circuit`. So for the moment we use `verify_proof` (not-conditional).
        // builder.conditionally_verify_proof_or_dummy::<C>(
        //     selector,
        //     &proof_targ,
        //     &verifier_data_targ,
        //     &common_data,
        // )?;

        Ok(SignatureTarget {
            selector,
            proof: proof_targ,
            pk: pk_targ,
            verifier_data_targ,
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

    // Note: this test must be run with the `--release` flag.
    #[test]
    fn test_signature_gate() -> Result<()> {
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

        let targets = SignatureGate {}.eval(&mut builder)?;
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
}
