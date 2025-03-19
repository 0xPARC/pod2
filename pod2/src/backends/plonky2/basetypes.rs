//! This file exposes the middleware::basetypes to be used in the middleware when the
//! `backend_plonky2` feature is enabled.
//! See src/middleware/basetypes.rs for more details.

use anyhow::{anyhow, Error, Result};
use hex::{FromHex, FromHexError};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::plonk::proof::Proof as Plonky2Proof;
use std::cmp::{Ord, Ordering};
use std::fmt;

use crate::middleware::{Params, ToFields};

use crate::backends::counter;

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;
/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
pub type C = PoseidonGoldilocksConfig;
/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

/// proof system proof
pub type Proof = Plonky2Proof<F, PoseidonGoldilocksConfig, D>;

pub const HASH_SIZE: usize = 4;
pub const VALUE_SIZE: usize = 4;

pub const EMPTY_VALUE: Value = Value([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
pub const SELF_ID_HASH: Hash = Hash([F::ONE, F::ZERO, F::ZERO, F::ZERO]);
pub const EMPTY_HASH: Hash = Hash([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct Value(pub [F; VALUE_SIZE]);

impl ToFields for Value {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        (self.0.to_vec(), VALUE_SIZE)
    }
}

impl Value {
    pub fn to_bytes(self) -> Vec<u8> {
        self.0
            .iter()
            .flat_map(|e| e.to_canonical_u64().to_le_bytes())
            .collect()
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        for (lhs, rhs) in self.0.iter().zip(other.0.iter()).rev() {
            let (lhs, rhs) = (lhs.to_canonical_u64(), rhs.to_canonical_u64());
            if lhs < rhs {
                return Ordering::Less;
            } else if lhs > rhs {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        let lo = F::from_canonical_u64((v as u64) & 0xffffffff);
        let hi = F::from_canonical_u64((v as u64) >> 32);
        Value([lo, hi, F::ZERO, F::ZERO])
    }
}

impl From<Hash> for Value {
    fn from(h: Hash) -> Self {
        Value(h.0)
    }
}

impl TryInto<i64> for Value {
    type Error = Error;
    fn try_into(self) -> std::result::Result<i64, Self::Error> {
        let value = self.0;
        if value[2..] != [F::ZERO, F::ZERO]
            || value[..2]
                .iter()
                .all(|x| x.to_canonical_u64() > u32::MAX as u64)
        {
            Err(anyhow!("Value not an element of the i64 embedding."))
        } else {
            Ok((value[0].to_canonical_u64() | (value[1].to_canonical_u64() << 32)) as i64)
        }
    }
}

impl fmt::Display for Value {
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

#[derive(Clone, Copy, Debug, Default, Hash, Eq, PartialEq)]
pub struct Hash(pub [F; HASH_SIZE]);

pub fn hash_value(input: &Value) -> Hash {
    hash_fields(&input.0)
}

pub fn hash_fields(input: &[F]) -> Hash {
    // Note: the counter counts when this method is called, but different input
    // sizes will have different costs in-circuit.
    counter::count_hash();
    Hash(PoseidonHash::hash_no_pad(&input).elements)
}

impl From<Value> for Hash {
    fn from(v: Value) -> Self {
        Hash(v.0)
    }
}
impl Hash {
    pub fn value(self) -> Value {
        Value(self.0)
    }
}

impl ToFields for Hash {
    fn to_fields(&self, _params: &Params) -> (Vec<F>, usize) {
        (self.0.to_vec(), VALUE_SIZE)
    }
}

impl Ord for Hash {
    fn cmp(&self, other: &Self) -> Ordering {
        Value(self.0).cmp(&Value(other.0))
    }
}

impl PartialOrd for Hash {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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

impl From<&str> for Hash {
    fn from(s: &str) -> Self {
        hash_str(s)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i64_value_roundtrip() {
        let test_cases = [
            0i64,
            1,
            -1,
            i64::MAX,
            i64::MIN,
            42,
            -42,
            1 << 32,
            -(1 << 32),
        ];

        for &original in test_cases.iter() {
            let value = Value::from(original);
            let roundtrip: i64 = value.try_into().unwrap();
            assert_eq!(original, roundtrip, "Failed roundtrip for {}", original);
        }
    }
}
