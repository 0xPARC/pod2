//! Fork from https://github.com/0xPolygonMiden/crypto/tree/aa45474377e978050958958d75688e7a8d46b628/miden-crypto/src/dsa/rpo_falcon512
//!
pub use miden_crypto::{
    hash::rpo::Rpo256,
    utils::{ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable},
};
use plonky2::field::types::Field;

use crate::backends::plonky2::basetypes::{Proof, Value, C, D, F, VALUE_SIZE};
pub use crate::backends::plonky2::basetypes::{Value as Word, F as Felt};

pub(crate) mod hash_to_point;
pub(crate) mod keys;
pub(crate) mod math;
pub(crate) mod signature;

pub use self::{
    keys::{PubKeyPoly, PublicKey, SecretKey},
    math::Polynomial,
    signature::{Signature, SignatureHeader, SignaturePoly},
};

// CONSTANTS
// ================================================================================================

// The Falcon modulus p.
pub(crate) const MODULUS: i16 = 12289;

// Number of bits needed to encode an element in the Falcon field.
pub(crate) const FALCON_ENCODING_BITS: u32 = 14;

// The Falcon parameters for Falcon-512. This is the degree of the polynomial `phi := x^N + 1`
// defining the ring Z_p[x]/(phi).
pub(crate) const N: usize = 512;
// pub(crate) const N: usize = 8;
const LOG_N: u8 = 9;

/// Length of nonce used for key-pair generation.
pub const SIG_NONCE_LEN: usize = 40;

/// Number of filed elements used to encode a nonce.
pub const NONCE_ELEMENTS: usize = 8;

/// Public key length as a u8 vector.
pub const PK_LEN: usize = 897;

/// Secret key length as a u8 vector.
pub const SK_LEN: usize = 1281;

/// Signature length as a u8 vector.
const SIG_POLY_BYTE_LEN: usize = 625;

/// Bound on the squared-norm of the signature.
const SIG_L2_BOUND: u64 = 34034726;

/// Standard deviation of the Gaussian over the lattice.
const SIGMA: f64 = 165.7366171829776;

// TYPE ALIASES
// ================================================================================================

type ShortLatticeBasis = [Polynomial<i16>; 4];

// NONCE
// ================================================================================================

/// Nonce of the Falcon signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Nonce([u8; SIG_NONCE_LEN]);

impl Nonce {
    /// Returns a new [Nonce] instantiated from the provided bytes.
    pub fn new(bytes: [u8; SIG_NONCE_LEN]) -> Self {
        Self(bytes)
    }

    /// Returns the underlying bytes of this nonce.
    pub fn as_bytes(&self) -> &[u8; SIG_NONCE_LEN] {
        &self.0
    }

    /// Converts byte representation of the nonce into field element representation.
    ///
    /// Nonce bytes are converted to field elements by taking consecutive 5 byte chunks
    /// of the nonce and interpreting them as field elements.
    pub fn to_elements(&self) -> [F; NONCE_ELEMENTS] {
        let mut buffer = [0_u8; 8];
        let mut result = [F::ZERO; 8];
        for (i, bytes) in self.0.chunks(5).enumerate() {
            buffer[..5].copy_from_slice(bytes);
            // we can safely (without overflow) create a new F from u64 value here since this
            // value contains at most 5 bytes
            result[i] = F::from_canonical_u64(u64::from_le_bytes(buffer));
        }

        result
    }
}

impl Serializable for &Nonce {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        target.write_bytes(&self.0)
    }
}

impl Deserializable for Nonce {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let bytes = source.read()?;
        Ok(Self(bytes))
    }
}
