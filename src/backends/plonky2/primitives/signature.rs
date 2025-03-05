//! Proof-based signatures, following https://eprint.iacr.org/2024/1553
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

pub struct ProverParams {
    prover: ProverCircuitData<F, C, D>,
    circuit: SignatureCircuit,
}

#[derive(Debug)]
pub struct VerifierParams(VerifierCircuitData<F, C, D>);

#[derive(Clone, Debug)]
pub struct SecretKey(Value);

#[derive(Clone, Debug)]
pub struct PublicKey(Value);

#[derive(Clone, Debug)]
pub struct Signature {
    s: Value,
    proof: Proof,
}

impl SecretKey {
    pub fn new() -> Self {
        // TODO review randomness
        Self(Value(std::array::from_fn(|_| F::rand())))
    }
    pub fn public_key(&self) -> PublicKey {
        PublicKey(Value(PoseidonHash::hash_no_pad(&self.0 .0).elements))
    }
    pub fn sign(&self, pp: &ProverParams, msg: Value) -> Result<Signature> {
        let pk = self.public_key();
        let s = Value(PoseidonHash::hash_no_pad(&[pk.0 .0, msg.0].concat()).elements);

        let mut pw = PartialWitness::<F>::new();
        pp.circuit.set_targets(&mut pw, self.clone(), pk, msg, s)?;

        let proof = pp.prover.prove(pw)?;

        Ok(Signature {
            s,
            proof: proof.proof,
        })
    }
}

impl Signature {
    pub fn params() -> Result<(ProverParams, VerifierParams)> {
        let (builder, circuit) = SignatureCircuit::builder()?;
        let prover = builder.build_prover::<C>();

        let (builder, _) = SignatureCircuit::builder()?;
        let circuit_data = builder.build::<C>();
        let vp = circuit_data.verifier_data();

        Ok((ProverParams { prover, circuit }, VerifierParams(vp)))
    }

    pub fn verify(&self, vp: &VerifierParams, pk: &PublicKey, msg: Value) -> Result<()> {
        let public_inputs: Vec<F> = [pk.0 .0, msg.0, self.s.0].concat();
        vp.0.verify(ProofWithPublicInputs {
            proof: self.proof.clone(),
            public_inputs,
        })
    }
}

struct SignatureCircuit {
    sk_targ: Vec<Target>,
    pk_targ: HashOutTarget,
    msg_targ: Vec<Target>,
    s_targ: HashOutTarget,
}

impl SignatureCircuit {
    fn builder() -> Result<(CircuitBuilder<F, D>, Self)> {
        // notice that we use the 'zk' config
        let config = CircuitConfig::standard_recursion_zk_config();

        let mut builder = CircuitBuilder::<F, D>::new(config);
        let circuit = Self::add_targets(&mut builder)?;

        Ok((builder, circuit))
    }

    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let sk_targ = builder.add_virtual_targets(VALUE_SIZE);
        let pk_targ = builder.add_virtual_hash();
        let msg_targ = builder.add_virtual_targets(VALUE_SIZE);
        let s_targ = builder.add_virtual_hash();

        builder.register_public_inputs(&pk_targ.elements);
        builder.register_public_inputs(&msg_targ);
        builder.register_public_inputs(&s_targ.elements);

        let computed_pk_targ = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sk_targ.clone());
        builder.connect_array::<VALUE_SIZE>(computed_pk_targ.elements, pk_targ.elements);

        let inp: Vec<Target> = [pk_targ.elements.to_vec(), msg_targ.clone()].concat();
        let computed_s_targ = builder.hash_n_to_hash_no_pad::<PoseidonHash>(inp);
        builder.connect_array::<VALUE_SIZE>(computed_s_targ.elements, s_targ.elements);

        Ok(Self {
            sk_targ,
            pk_targ,
            msg_targ,
            s_targ,
        })
    }

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
    use std::time::Instant;

    use super::*;

    // Note: this test must be run with the `--release` flag.
    #[test]
    fn test_signature() -> Result<()> {
        let sk = SecretKey::new();
        let pk = sk.public_key();

        let msg = Value::from(42);

        let start = Instant::now();
        let (pp, vp) = Signature::params()?;
        println!("Signature::params(): {:?}", start.elapsed());

        let start = Instant::now();
        let sig = sk.sign(&pp, msg)?;
        println!("sk.sign(): {:?}", start.elapsed());

        let start = Instant::now();
        sig.verify(&vp, &pk, msg)?;
        println!("sig.verify(): {:?}", start.elapsed());

        // perform a 2nd signature and verify it
        let msg_2 = Value::from(1000);
        let sig2 = sk.sign(&pp, msg_2)?;
        sig2.verify(&vp, &pk, msg_2)?;

        Ok(())
    }
}
