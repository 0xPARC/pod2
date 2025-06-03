//! This file exposes the basetypes to be used in the middleware when the `backend_plonky2` feature
//! is enabled.
//! See src/middleware/basetypes.rs for more details.

use plonky2::{
    field::{extension::quadratic::QuadraticExtension, goldilocks_field::GoldilocksField},
    hash::poseidon::PoseidonHash,
    plonk::{circuit_builder, circuit_data, config::GenericConfig, proof},
};
use serde::Serialize;

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;

/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

/// FE is the degree D field extension used in Plonky2 proofs.
pub type FE = QuadraticExtension<F>;

/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
#[derive(Debug, Copy, Clone, Default, Eq, PartialEq, Serialize)]
pub struct C;
impl GenericConfig<D> for C {
    type F = F;
    type FE = FE;
    type Hasher = PoseidonHash;
    type InnerHasher = PoseidonHash;
}

pub type CircuitData = circuit_data::CircuitData<F, C, D>;
pub type CommonCircuitData = circuit_data::CommonCircuitData<F, D>;
pub type ProverOnlyCircuitData = circuit_data::ProverOnlyCircuitData<F, C, D>;
pub type VerifierOnlyCircuitData = circuit_data::VerifierOnlyCircuitData<C, D>;
pub type VerifierCircuitData = circuit_data::VerifierCircuitData<F, C, D>;
pub type CircuitBuilder = circuit_builder::CircuitBuilder<F, D>;
pub type Proof = proof::Proof<F, C, D>;
pub type ProofWithPublicInputs = proof::ProofWithPublicInputs<F, C, D>;
