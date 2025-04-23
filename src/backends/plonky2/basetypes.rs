//! This file exposes the middleware::basetypes to be used in the middleware when the
//! `backend_plonky2` feature is enabled.
//! See src/middleware/basetypes.rs for more details.

use plonky2::plonk::{config::PoseidonGoldilocksConfig, proof::Proof as Plonky2Proof};

use crate::middleware::F;

/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
pub type C = PoseidonGoldilocksConfig;
/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

/// proof system proof
pub type Proof = Plonky2Proof<F, PoseidonGoldilocksConfig, D>;
