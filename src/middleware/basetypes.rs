// TODO: Update this doc
//! This file exposes the backend dependent basetypes as middleware types,
//! taking them from the feature-enabled backend.
//!
//! This is done in order to avoid inconsistencies where a type or parameter is
//! defined in the middleware to have certain carachteristic and later in the
//! backend it gets used differently. The idea is that those types and
//! parameters (eg. lengths) have a single source of truth in the code; and in
//! the case of the "base types" this is determined by the backend being used
//! under the hood, not by a choice of the middleware parameters.
//!
//! The idea with this approach, is that the frontend & middleware should not
//! need to import the proving library used by the backend (eg. plonky2,
//! plonky3, etc).
//!
//! For example, the `Hash` and `Value` types are types belonging at the
//! middleware, and is the middleware who reasons about them, but depending on
//! the backend being used, the `Hash` and `Value` types will have different
//! sizes. So it's the backend being used who actually defines their nature
//! under the hood. For example with a plonky2 backend, these types will have a
//! length of 4 field elements, whereas with a plonky3 backend they will have a
//! length of 8 field eleements.
//!
//! Note that his approach does not introduce new traits or abstract code,
//! just makes use of rust features to define 'base types' that are being used
//! in the middleware.
//!
//!
//! NOTE (TMP): current implementation still uses plonky2 in the middleware for
//! u64/i64 to F conversion. Eventually we will do those conversions through the
//! approach described in this file, removing the imports of plonky2 in the
//! middleware.
//! TODO: Update this doc

/// Value, Hash and F are imported based on 'features'. For example by default
/// we use the 'plonky2' feature, but it could be used a 'plonky3' feature, so
/// then the Value, Hash and F types would come from the plonky3 backend.
// #[cfg(feature = "backend_plonky2")]
// pub use crate::backends::plonky2::basetypes::{
//     hash_fields, hash_str, hash_value, Hash, RawValue, EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE,
//     SELF_ID_HASH, VALUE_SIZE,
// };
use std::{
    cmp::{Ord, Ordering},
    fmt,
};

use anyhow::Result;
use hex::{FromHex, FromHexError};
use plonky2::{
    field::{
        goldilocks_field::GoldilocksField,
        types::{Field, PrimeField64},
    },
    hash::poseidon::PoseidonHash,
    plonk::config::Hasher,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use super::serialization::*;
use crate::middleware::{Params, ToFields};

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;

pub const HASH_SIZE: usize = 4;
pub const VALUE_SIZE: usize = 4;

pub const EMPTY_VALUE: RawValue = RawValue([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
pub const SELF_ID_HASH: Hash = Hash([F::ONE, F::ZERO, F::ZERO, F::ZERO]);
pub const EMPTY_HASH: Hash = Hash([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct RawValue(
    #[serde(
        serialize_with = "serialize_value_tuple",
        deserialize_with = "deserialize_value_tuple"
    )]
    // We know that Serde will serialize and deserialize this as a string, so we can
    // use the JsonSchema to validate the format.
    #[schemars(with = "String", regex(pattern = r"^[0-9a-fA-F]{64}$"))]
    pub [F; VALUE_SIZE],
);

impl ToFields for RawValue {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        self.0.to_vec()
    }
}

impl RawValue {
    pub fn to_bytes(self) -> Vec<u8> {
        self.0
            .iter()
            .flat_map(|e| e.to_canonical_u64().to_le_bytes())
            .collect()
    }
}

impl Ord for RawValue {
    fn cmp(&self, other: &Self) -> Ordering {
        for (lhs, rhs) in self.0.iter().zip(other.0.iter()).rev() {
            let (lhs, rhs) = (lhs.to_canonical_u64(), rhs.to_canonical_u64());
            match lhs.cmp(&rhs) {
                Ordering::Less => return Ordering::Less,
                Ordering::Greater => return Ordering::Greater,
                _ => {}
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for RawValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<i64> for RawValue {
    fn from(v: i64) -> Self {
        let lo = F::from_canonical_u64((v as u64) & 0xffffffff);
        let hi = F::from_canonical_u64((v as u64) >> 32);
        RawValue([lo, hi, F::ZERO, F::ZERO])
    }
}

impl From<Hash> for RawValue {
    fn from(h: Hash) -> Self {
        RawValue(h.0)
    }
}

impl fmt::Display for RawValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0[2].is_zero() && self.0[3].is_zero() {
            // Assume this is an integer
            let (l0, l1) = (self.0[0].to_canonical_u64(), self.0[1].to_canonical_u64());
            assert!(l0 < (1 << 32));
            assert!(l1 < (1 << 32));
            write!(f, "{}", l0 + l1 * (1 << 32))
        } else {
            // Assume this is a hash
            Hash(self.0).fmt(f)
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Hash, Eq, PartialEq, Serialize, Deserialize, JsonSchema)]
pub struct Hash(
    #[serde(
        serialize_with = "serialize_hash_tuple",
        deserialize_with = "deserialize_hash_tuple"
    )]
    #[schemars(with = "String", regex(pattern = r"^[0-9a-fA-F]{64}$"))]
    pub [F; HASH_SIZE],
);

pub fn hash_value(input: &RawValue) -> Hash {
    hash_fields(&input.0)
}

pub fn hash_fields(input: &[F]) -> Hash {
    Hash(PoseidonHash::hash_no_pad(input).elements)
}

impl From<RawValue> for Hash {
    fn from(v: RawValue) -> Self {
        Hash(v.0)
    }
}

impl ToFields for Hash {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        self.0.to_vec()
    }
}

impl PartialOrd for Hash {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Hash {
    fn cmp(&self, other: &Self) -> Ordering {
        RawValue(self.0).cmp(&RawValue(other.0))
    }
}

impl fmt::Display for Hash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v0 = self.0[0].to_canonical_u64();
        for i in 0..HASH_SIZE {
            write!(f, "{:02x}", (v0 >> (i * 8)) & 0xff)?;
        }
        write!(f, "…")
    }
}

impl FromHex for Hash {
    type Error = FromHexError;

    // TODO make it dependant on backend::Value len
    fn from_hex<T: AsRef<[u8]>>(hex: T) -> Result<Self, Self::Error> {
        // In little endian
        let bytes = <[u8; 32]>::from_hex(hex)?;
        let mut buf: [u8; 8] = [0; 8];
        let mut inner = [F::ZERO; HASH_SIZE];
        for i in 0..HASH_SIZE {
            buf.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
            inner[i] = F::from_canonical_u64(u64::from_le_bytes(buf));
        }
        Ok(Self(inner))
    }
}

pub fn hash_str(s: &str) -> Hash {
    let mut input = s.as_bytes().to_vec();
    input.push(1); // padding

    // Merge 7 bytes into 1 field, because the field is slightly below 64 bits
    let input: Vec<F> = input
        .chunks(7)
        .map(|bytes| {
            let mut v: u64 = 0;
            for b in bytes.iter().rev() {
                v <<= 8;
                v += *b as u64;
            }
            F::from_canonical_u64(v)
        })
        .collect();
    hash_fields(&input)
}
