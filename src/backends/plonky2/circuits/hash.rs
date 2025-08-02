use plonky2::{
    hash::{
        hash_types::{HashOutTarget, RichField, NUM_HASH_OUT_ELTS},
        hashing::PlonkyPermutation,
    },
    iop::target::Target,
    plonk::config::AlgebraicHasher,
};

use crate::{backends::plonky2::basetypes::CircuitBuilder, middleware::F};

/// Precompute the hash state by absorbing all full chunks from `inputs` and return the reminder
/// elements that didn't fit into a chunk.
pub fn precompute_hash_state<F: RichField, P: PlonkyPermutation<F>>(inputs: &[F]) -> (P, &[F]) {
    let (inputs, inputs_rem) = inputs.split_at((inputs.len() / P::RATE) * P::RATE);
    let mut perm = P::new(core::iter::repeat(F::ZERO));

    // Absorb all inputs up to the biggest multiple of RATE.
    for input_chunk in inputs.chunks(P::RATE) {
        perm.set_from_slice(input_chunk, 0);
        perm.permute();
    }

    (perm, inputs_rem)
}

/// Hash `inputs` starting from a circuit-constant `perm` state.
pub fn hash_from_state_circuit<H: AlgebraicHasher<F>, P: PlonkyPermutation<F>>(
    builder: &mut CircuitBuilder,
    perm: P,
    inputs: &[Target],
) -> HashOutTarget {
    let mut state =
        H::AlgebraicPermutation::new(perm.as_ref().iter().map(|v| builder.constant(*v)));

    // Absorb all input chunks.
    for input_chunk in inputs.chunks(H::AlgebraicPermutation::RATE) {
        // Overwrite the first r elements with the inputs. This differs from a standard sponge,
        // where we would xor or add in the inputs. This is a well-known variant, though,
        // sometimes called "overwrite mode".
        state.set_from_slice(input_chunk, 0);
        state = builder.permute::<H>(state);
    }

    let num_outputs = NUM_HASH_OUT_ELTS;
    // Squeeze until we have the desired number of outputs.
    let mut outputs = Vec::with_capacity(num_outputs);
    loop {
        for &s in state.squeeze() {
            outputs.push(s);
            if outputs.len() == num_outputs {
                return HashOutTarget::from_vec(outputs);
            }
        }
        state = builder.permute::<H>(state);
    }
}
