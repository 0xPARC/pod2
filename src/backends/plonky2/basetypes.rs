//! This file exposes the middleware::basetypes to be used in the middleware when the
//! `backend_plonky2` feature is enabled.
//! See src/middleware/basetypes.rs for more details.

use std::{
    cmp::{Ord, Ordering},
    fmt,
};

use anyhow::{anyhow, Error, Result};
use hex::{FromHex, FromHexError};
use plonky2::{
    field::{
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField64},
    },
    hash::poseidon::PoseidonHash,
    plonk::{
        config::{Hasher, PoseidonGoldilocksConfig},
        proof::Proof as Plonky2Proof,
    },
};

// use schemars::JsonSchema;
// use serde::{Deserialize, Serialize};
use crate::middleware::{
    // serialization::{
    //     deserialize_hash_tuple, deserialize_value_tuple, serialize_hash_tuple,
    //     serialize_value_tuple,
    // },
    Params,
    ToFields,
};

/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
pub type C = PoseidonGoldilocksConfig;
/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

/// proof system proof
pub type Proof = Plonky2Proof<F, PoseidonGoldilocksConfig, D>;
