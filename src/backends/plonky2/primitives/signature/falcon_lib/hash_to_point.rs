//! Fork from https://github.com/0xPolygonMiden/crypto/tree/aa45474377e978050958958d75688e7a8d46b628/miden-crypto/src/dsa/rpo_falcon512
//!
// use alloc::vec::Vec;

// HASH-TO-POINT FUNCTIONS
// ================================================================================================
use core::ops::Range;

use num::Zero;
use plonky2::{
    field::types::Field,
    hash::{
        hashing::PlonkyPermutation,
        poseidon::{Poseidon, PoseidonHash, PoseidonPermutation},
    },
};

use super::{math::FalconFelt, Nonce, Polynomial, Rpo256, Word, MODULUS, N};
use crate::middleware::F;
pub(crate) const RATE_RANGE: Range<usize> = 4..12; // TODO review

/// Returns a polynomial in Z_p[x]/(phi) representing the hash of the provided
/// message and nonce using Poseidon.
pub fn hash_to_point(message: Word, nonce: &Nonce) -> Polynomial<FalconFelt> {
    let mut state: [F; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH] =
        [F::ZERO; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];

    // absorb the nonce into the state
    let nonce_elements = nonce.to_elements();
    for (&n, s) in nonce_elements.iter().zip(state.iter_mut()) {
        *s = n;
    }
    state = F::poseidon(state);

    // absorb message into the state
    for (&m, s) in message.0.iter().zip(state[RATE_RANGE].iter_mut()) {
        *s = m;
    }

    // squeeze the coefficients of the polynomial
    let mut i = 0;
    let mut res = [FalconFelt::zero(); N];
    for _ in 0..64 {
        state = F::poseidon(state);
        for a in &state[RATE_RANGE] {
            res[i] = FalconFelt::new((a.0 % MODULUS as u64) as i16);
            i += 1;
        }
    }

    Polynomial::new(res.to_vec())
}
