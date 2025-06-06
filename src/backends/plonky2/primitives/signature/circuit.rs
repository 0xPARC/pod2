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

pub struct SignatureVerifyGadget;

pub struct SignatureVerifyTarget {
    // `enabled` determines if the signature verification is enabled
    pub(crate) enabled: BoolTarget,
    pub(crate) pk: PointTarget,
    pub(crate) msg: ValueTarget,
    // proof of the SignatureInternalCircuit (=signature::Signature.0)
    pub(crate) sig: SignatureTarget,
}

impl SignatureVerifyGadget {
    /// creates the targets and defines the logic of the circuit
    pub fn eval(&self, builder: &mut CircuitBuilder<F, D>) -> Result<SignatureVerifyTarget> {
        let measure = measure_gates_begin!(builder, "SignatureVerify");
        let enabled = builder.add_virtual_bool_target_safe();
        let pk = builder.add_virtual_point_target();
        let msg = builder.add_virtual_value();
        let sig = builder.add_virtual_schnorr_signature_target();

        let verified = sig.verify(builder, HashOutTarget::from(msg.elements), &pk);

        let result = builder.mul_sub(enabled.target, verified.target, enabled.target);

        builder.assert_zero(result);

        measure_gates_end!(builder, measure);
        Ok(SignatureVerifyTarget {
            enabled,
            pk,
            msg,
            sig,
        })
    }
}

impl SignatureVerifyTarget {
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

        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
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
        let mut pw = PartialWitness::<F>::new();
        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
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

        let targets = SignatureVerifyGadget {}.eval(&mut builder)?;
        targets.set_targets(&mut pw, false, pk, msg, sig)?; // enabled=false

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }
}
