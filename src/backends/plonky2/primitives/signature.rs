//! Proof-based signatures using Plonky2 proofs, following
//! https://eprint.iacr.org/2024/1553 .
use anyhow::Result;
use plonky2::{
    field::types::Sample,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, ProverCircuitData, VerifierCircuitData},
        config::Hasher,
        proof::ProofWithPublicInputs,
    },
};

use crate::backends::plonky2::basetypes::{Proof, Value, C, D, F, VALUE_SIZE};

use lazy_static::lazy_static;

lazy_static! {
    static ref PP: ProverParams = Signature::prover_params().unwrap();
    static ref VP: VerifierParams = Signature::verifier_params().unwrap();
}

pub struct ProverParams {
    prover: ProverCircuitData<F, C, D>,
    circuit: SignatureCircuit,
}

#[derive(Clone, Debug)]
pub struct VerifierParams(VerifierCircuitData<F, C, D>);

#[derive(Clone, Debug)]
pub struct SecretKey(Value);

#[derive(Clone, Debug)]
pub struct PublicKey(pub(crate) Value);

#[derive(Clone, Debug)]
pub struct Signature(pub(crate) Proof);

/// Implements the key generation and the computation of proof-based signatures.
impl SecretKey {
    pub fn new() -> Self {
        // note: the `F::rand()` internally uses `rand::rngs::OsRng`
        Self(Value(std::array::from_fn(|_| F::rand())))
    }

    pub fn public_key(&self) -> PublicKey {
        PublicKey(Value(PoseidonHash::hash_no_pad(&self.0 .0).elements))
    }

    pub fn sign(&self, msg: Value) -> Result<Signature> {
        let pk = self.public_key();
        let s = Value(PoseidonHash::hash_no_pad(&[pk.0 .0, msg.0].concat()).elements);

        let mut pw = PartialWitness::<F>::new();
        PP.circuit.set_targets(&mut pw, self.clone(), pk, msg, s)?;

        let proof = PP.prover.prove(pw)?;

        Ok(Signature(proof.proof))
    }
}

/// Implements the parameters generation and the verification of proof-based
/// signatures.
impl Signature {
    pub fn prover_params() -> Result<ProverParams> {
        let (builder, circuit) = Self::builder()?;
        let prover = builder.build_prover::<C>();
        Ok(ProverParams { prover, circuit })
    }
    pub fn verifier_params() -> Result<VerifierParams> {
        let (builder, _) = Self::builder()?;
        let circuit_data = builder.build::<C>();
        let vp = circuit_data.verifier_data();

        Ok(VerifierParams(vp))
    }
    pub fn params() -> Result<(ProverParams, VerifierParams)> {
        let pp = Self::prover_params()?;
        let vp = Self::verifier_params()?;
        Ok((pp, vp))
    }

    fn builder() -> Result<(CircuitBuilder<F, D>, SignatureCircuit)> {
        // notice that we use the 'zk' config
        let config = CircuitConfig::standard_recursion_zk_config();

        let mut builder = CircuitBuilder::<F, D>::new(config);
        let circuit = SignatureCircuit::add_targets(&mut builder)?;

        Ok((builder, circuit))
    }

    pub fn verify(&self, pk: &PublicKey, msg: Value) -> Result<()> {
        // prepare public inputs as [pk, msg, s]
        let s = Value(PoseidonHash::hash_no_pad(&[pk.0 .0, msg.0].concat()).elements);
        let public_inputs: Vec<F> = [pk.0 .0, msg.0, s.0].concat();

        // verify plonky2 proof
        VP.0.verify(ProofWithPublicInputs {
            proof: self.0.clone(),
            public_inputs,
        })
    }
}

/// The SignatureCircuit implements the circuit used for the proof of the
/// argument described at https://eprint.iacr.org/2024/1553.
///
/// The circuit proves that for the given public inputs (pk, msg, s), the Prover
/// knows the secret (sk) such that:
/// i) pk == H(sk)
/// ii) s == H(pk, msg)
struct SignatureCircuit {
    sk_targ: Vec<Target>,
    pk_targ: HashOutTarget,
    msg_targ: Vec<Target>,
    s_targ: HashOutTarget,
}

impl SignatureCircuit {
    /// creates the targets and defines the logic of the circuit
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        // create the targets
        let sk_targ = builder.add_virtual_targets(VALUE_SIZE);
        let pk_targ = builder.add_virtual_hash();
        let msg_targ = builder.add_virtual_targets(VALUE_SIZE);
        let s_targ = builder.add_virtual_hash();

        // define the public inputs
        builder.register_public_inputs(&pk_targ.elements);
        builder.register_public_inputs(&msg_targ);
        builder.register_public_inputs(&s_targ.elements);

        // define the logic
        let computed_pk_targ = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sk_targ.clone());
        builder.connect_array::<VALUE_SIZE>(computed_pk_targ.elements, pk_targ.elements);

        let inp: Vec<Target> = [pk_targ.elements.to_vec(), msg_targ.clone()].concat();
        let computed_s_targ = builder.hash_n_to_hash_no_pad::<PoseidonHash>(inp);
        builder.connect_array::<VALUE_SIZE>(computed_s_targ.elements, s_targ.elements);

        // return the targets
        Ok(Self {
            sk_targ,
            pk_targ,
            msg_targ,
            s_targ,
        })
    }

    /// assigns the given values to the targets
    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        sk: SecretKey,
        pk: PublicKey,
        msg: Value,
        s: Value,
    ) -> Result<()> {
        pw.set_target_arr(&self.sk_targ, &sk.0 .0.to_vec())?;
        pw.set_hash_target(self.pk_targ, HashOut::<F>::from_vec(pk.0 .0.to_vec()))?;
        pw.set_target_arr(&self.msg_targ, &msg.0.to_vec())?;
        pw.set_hash_target(self.s_targ, HashOut::<F>::from_vec(s.0.to_vec()))?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use crate::backends::plonky2::basetypes::Hash;

    use super::*;

    // Note: this test must be run with the `--release` flag.
    #[test]
    fn test_signature() -> Result<()> {
        let sk = SecretKey::new();
        let pk = sk.public_key();

        let msg = Value::from(42);
        let sig = sk.sign(msg)?;
        sig.verify(&pk, msg)?;

        // expect the signature verification to fail when using a different msg
        let v = sig.verify(&pk, Value::from(24));
        assert!(v.is_err(), "should fail to verify");

        // perform a 2nd signature over another msg and verify it
        let msg_2 = Value::from(Hash::from("message"));
        let sig2 = sk.sign(msg_2)?;
        sig2.verify(&pk, msg_2)?;

        Ok(())
    }
}
