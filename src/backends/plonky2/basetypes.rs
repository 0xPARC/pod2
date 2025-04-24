//! This file exposes the middleware::basetypes to be used in the middleware when the
//! `backend_plonky2` feature is enabled.
//! See src/middleware/basetypes.rs for more details.

use plonky2::{
    field::extension::quadratic::QuadraticExtension,
    hash::poseidon::PoseidonHash,
    plonk::{config::GenericConfig, proof::Proof as Plonky2Proof},
};
use serde::Serialize;

use crate::middleware::F;

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

/// proof system proof
pub type Proof = Plonky2Proof<F, C, D>;
