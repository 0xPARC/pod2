//! Falcon signatures https://falcon-sign.info over the Goldilocks field.
//! This module is a wrapper on top of Miden's Falcon rust implementation:
//! https://github.com/0xPolygonMiden/crypto/tree/aa45474377e978050958958d75688e7a8d46b628/miden-crypto/src/dsa/rpo_falcon512/signature.rs#L49
//!

pub use super::falcon_lib::{PublicKey, SecretKey, Signature};

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::{
        field::types::{Field, Sample},
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
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::{PublicKey, SecretKey, Signature};
    use crate::backends::plonky2::basetypes::{Proof, Value, C, D, F, VALUE_SIZE};

    #[test]
    fn test_falcon() {
        let seed = [0_u8; 32];
        let mut rng = ChaCha20Rng::from_seed(seed);

        // generate random keys
        let sk = SecretKey::with_rng(&mut rng);
        let pk = sk.public_key();

        // sign a random message
        let message: Value = Value([F::ONE; 4]);
        let signature = sk.sign_with_rng(message, &mut rng);

        // make sure the signature verifies correctly
        assert!(pk.verify(message, &signature));

        // a signature should not verify against a wrong message
        let message2: Value = Value([F::ONE.double(); 4]);
        assert!(!pk.verify(message2, &signature));

        // a signature should not verify against a wrong public key
        let sk2 = SecretKey::with_rng(&mut rng);
        assert!(!sk2.public_key().verify(message, &signature))
    }
}
