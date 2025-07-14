#![allow(unused)]
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
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, ProverCircuitData, VerifierCircuitData,
            VerifierCircuitTarget,
        },
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        circuits::common::{CircuitBuilderPod, ValueTarget},
        error::Result,
        primitives::ec::{
            curve::{CircuitBuilderElliptic, Point, PointTarget, WitnessWriteCurve},
            schnorr::{CircuitBuilderSchnorr, Signature, SignatureTarget, WitnessWriteSchnorr},
        },
    },
    measure_gates_begin, measure_gates_end,
    middleware::{Hash, Proof, RawValue, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE},
};

// TODO: This is a very simple wrapper over the signature verification implemented on
// `SignatureTarget`.  I think we can remove this and use it directly.  Also we're not using the
// `enabled` flag, so it should be straight-forward to remove this.
pub struct SignatureVerifyTarget {
    // `enabled` determines if the signature verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) pk: PointTarget,
    pub(crate) msg: ValueTarget,
    // proof of the SignatureInternalCircuit (=signature::Signature.0)
    pub(crate) sig: SignatureTarget,
}

pub fn verify_signature_circuit(
    builder: &mut CircuitBuilder<F, D>,
    signature: &SignatureVerifyTarget,
) {
    let measure = measure_gates_begin!(builder, "SignatureVerify");
    let verified = signature.sig.verify(
        builder,
        HashOutTarget::from(signature.msg.elements),
        &signature.pk,
    );
    let result = builder.mul_sub(
        signature.enabled.target,
        verified.target,
        signature.enabled.target,
    );
    builder.assert_zero(result);
    measure_gates_end!(builder, measure);
}

impl SignatureVerifyTarget {
    pub fn new_virtual(builder: &mut CircuitBuilder<F, D>) -> Self {
        SignatureVerifyTarget {
            enabled: builder.add_virtual_bool_target_safe(),
            pk: builder.add_virtual_point_target(),
            msg: builder.add_virtual_value(),
            sig: builder.add_virtual_schnorr_signature_target(),
        }
    }
    /// assigns the given values to the targets
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        enabled: bool,
        pk: Point,
        msg: RawValue,
        signature: Signature,
    ) -> Result<()> {
        pw.set_bool_target(self.enabled, enabled)?;
        pw.set_point_target(&self.pk, &pk)?;
        pw.set_target_arr(&self.msg.elements, &msg.0)?;
        pw.set_signature_target(&self.sig, &signature)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use num_bigint::RandBigInt;

    use super::*;
    use crate::{
        backends::plonky2::primitives::ec::{curve::GROUP_ORDER, schnorr::SecretKey},
        middleware::Hash,
    };

    #[test]
    fn test_signature_gadget_enabled() -> Result<()> {
        // generate a valid signature
        let sk = SecretKey::new_rand();
        let pk = sk.public_key();
        let msg = RawValue::from(42);
        let nonce = 1337u64.into();
        let sig = sk.sign(msg, &nonce);
        assert!(sig.verify(pk, msg), "Should verify");

        // circuit
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = SignatureVerifyTarget::new_virtual(&mut builder);
        verify_signature_circuit(&mut builder, &targets);
        targets.set_targets(&mut pw, true, pk, msg, sig)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_signature_gadget_disabled() -> Result<()> {
        // generate a valid signature
        let sk = SecretKey::new_rand();
        let pk = sk.public_key();
        let msg = RawValue::from(42);
        let nonce = 600613u64.into();
        let sig = sk.sign(msg, &nonce);
        // verification should pass
        let v = sig.verify(pk, msg);
        assert!(v, "should verify");

        // replace the message, so that verifications should fail
        let msg = RawValue::from(24);
        // expect signature native verification to fail
        let v = sig.verify(pk, RawValue::from(24));
        assert!(!v, "should fail to verify");

        // circuit
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let targets = SignatureVerifyTarget::new_virtual(&mut builder);
        verify_signature_circuit(&mut builder, &targets);
        let mut pw = PartialWitness::<F>::new();
        targets.set_targets(&mut pw, true, pk, msg, sig.clone())?; // enabled=true

        // generate proof, and expect it to fail
        let data = builder.build::<C>();
        assert!(data.prove(pw).is_err()); // expect prove to fail

        // build the circuit again, but now disable the selector ('enabled')
        // that disables the in-circuit signature verification (ie.
        // `enabled=false`)
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = SignatureVerifyTarget::new_virtual(&mut builder);
        verify_signature_circuit(&mut builder, &targets);
        targets.set_targets(&mut pw, false, pk, msg, sig)?; // enabled=false

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }
}
