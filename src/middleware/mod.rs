//! The middleware includes the type definitions and the traits used to connect the frontend and
//! the backend.

mod custom;
mod operation;
mod statement;
pub use custom::*;
pub use operation::*;
pub use statement::*;

use anyhow::{anyhow, Error, Result};
use dyn_clone::DynClone;
use hex::{FromHex, FromHexError};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::{Hasher, PoseidonGoldilocksConfig};
use std::any::Any;
use std::cmp::{Ord, Ordering};
use std::collections::HashMap;
use std::fmt;

pub mod containers;

/// F is the native field we use everywhere.  Currently it's Goldilocks from plonky2
pub type F = GoldilocksField;
/// C is the Plonky2 config used in POD2 to work with Plonky2 recursion.
pub type C = PoseidonGoldilocksConfig;
/// D defines the extension degree of the field used in the Plonky2 proofs (quadratic extension).
pub const D: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// AnchoredKey is a tuple containing (OriginId: PodId, key: Hash)
pub struct AnchoredKey(pub PodId, pub Hash);

impl AnchoredKey {
    pub fn origin(&self) -> PodId {
        self.0
    }
    pub fn key(&self) -> Hash {
        self.1
    }
}

/// An entry consists of a key-value pair.
pub type Entry = (String, Value);

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct Value(pub [F; 4]);

impl ToFields for Value {
    fn to_fields(self) -> (Vec<F>, usize) {
        (self.0.to_vec(), 4)
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
        return Ordering::Equal;
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
        if &value[2..] != &[F::ZERO, F::ZERO]
            || value[..2]
                .iter()
                .all(|x| x.to_canonical_u64() > u32::MAX as u64)
        {
            Err(anyhow!("Value not an element of the i64 embedding."))
        } else {
            Ok((value[0].to_canonical_u64() + value[1].to_canonical_u64() << 32) as i64)
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
pub struct Hash(pub [F; 4]);

impl ToFields for Hash {
    fn to_fields(self) -> (Vec<F>, usize) {
        (self.0.to_vec(), 4)
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

pub const EMPTY: Value = Value([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
pub const NULL: Hash = Hash([F::ZERO, F::ZERO, F::ZERO, F::ZERO]);

impl fmt::Display for Hash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v0 = self.0[0].to_canonical_u64();
        for i in 0..4 {
            write!(f, "{:02x}", (v0 >> (i * 8)) & 0xff)?;
        }
        write!(f, "…")
    }
}

impl FromHex for Hash {
    type Error = FromHexError;

    fn from_hex<T: AsRef<[u8]>>(hex: T) -> Result<Self, Self::Error> {
        // In little endian
        let bytes = <[u8; 32]>::from_hex(hex)?;
        let mut buf: [u8; 8] = [0; 8];
        let mut inner = [F::ZERO; 4];
        for i in 0..4 {
            buf.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
            inner[i] = F::from_canonical_u64(u64::from_le_bytes(buf));
        }
        Ok(Self(inner))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct PodId(pub Hash);

impl ToFields for PodId {
    fn to_fields(self) -> (Vec<F>, usize) {
        self.0.to_fields()
    }
}

pub const SELF: PodId = PodId(Hash([F::ONE, F::ZERO, F::ZERO, F::ZERO]));

impl fmt::Display for PodId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == SELF {
            write!(f, "self")
        } else if self.0 == NULL {
            write!(f, "null")
        } else {
            write!(f, "{}", self.0)
        }
    }
}

pub enum PodType {
    None = 0,
    MockSigned = 1,
    MockMain = 2,
    Signed = 3,
    Main = 4,
}

impl From<PodType> for Value {
    fn from(v: PodType) -> Self {
        Value::from(v as i64)
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
    Hash(PoseidonHash::hash_no_pad(&input).elements)
}

#[derive(Clone, Debug, Copy)]
pub struct Params {
    pub max_input_signed_pods: usize,
    pub max_input_main_pods: usize,
    pub max_statements: usize,
    pub max_signed_pod_values: usize,
    pub max_public_statements: usize,
    pub max_statement_args: usize,
    pub max_operation_args: usize,
}

impl Params {
    pub fn max_priv_statements(&self) -> usize {
        self.max_statements - self.max_public_statements
    }
}

impl Default for Params {
    fn default() -> Self {
        Self {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 20,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 5,
            max_operation_args: 5,
        }
    }
}

pub trait Pod: fmt::Debug + DynClone {
    fn verify(&self) -> bool;
    fn id(&self) -> PodId;
    fn pub_statements(&self) -> Vec<Statement>;
    /// Extract key-values from ValueOf public statements
    fn kvs(&self) -> HashMap<AnchoredKey, Value> {
        self.pub_statements()
            .into_iter()
            .filter_map(|st| match st {
                Statement::ValueOf(ak, v) => Some((ak, v)),
                _ => None,
            })
            .collect()
    }
    // Used for downcasting
    fn into_any(self: Box<Self>) -> Box<dyn Any>;
}

// impl Clone for Box<dyn SignedPod>
dyn_clone::clone_trait_object!(Pod);

pub trait PodSigner {
    fn sign(&mut self, params: &Params, kvs: &HashMap<Hash, Value>) -> Result<Box<dyn Pod>>;
}

/// This is a filler type that fulfills the Pod trait and always verifies.  It's empty.  This
/// can be used to simulate padding in a circuit.
#[derive(Debug, Clone)]
pub struct NonePod {}

impl Pod for NonePod {
    fn verify(&self) -> bool {
        true
    }
    fn id(&self) -> PodId {
        PodId(NULL)
    }
    fn pub_statements(&self) -> Vec<Statement> {
        Vec::new()
    }
    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

#[derive(Debug)]
pub struct MainPodInputs<'a> {
    pub signed_pods: &'a [&'a Box<dyn Pod>],
    pub main_pods: &'a [&'a Box<dyn Pod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    /// Statements that need to be made public (they can come from input pods or input
    /// statements)
    pub public_statements: &'a [Statement],
}

pub trait PodProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>>;
}

pub trait ToFields {
    /// returns Vec<F> representation of the type, and a usize indicating how many field elements
    /// does the vector contain
    fn to_fields(self) -> (Vec<F>, usize);
}
