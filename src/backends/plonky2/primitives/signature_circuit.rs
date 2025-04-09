//! This file implements the Plonky2 circuit which verifies the Falcon signatures
//! (https://falcon-sign.info). Compatible with the signatures generated by signature.rs.
//!

use anyhow::Result;
use plonky2::{
    field::types::{Field, Field64, PrimeField64},
    hash::{
        hash_types::{HashOut, HashOutTarget},
        hashing::PlonkyPermutation,
        poseidon::{Poseidon, PoseidonHash, PoseidonPermutation},
    },
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, ProverCircuitData, VerifierCircuitData,
            VerifierCircuitTarget,
        },
        config::{AlgebraicHasher, Hasher},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};
use plonky2::iop::generator::SimpleGenerator;
 use plonky2::iop::witness::PartitionWitness;
use plonky2::iop::generator::GeneratedValues;
use plonky2::plonk::circuit_data::CommonCircuitData;
use plonky2::util::serialization::{Buffer, IoResult, Read, Write};
use plonky2::iop::witness::Witness;

use crate::backends::plonky2::{
    basetypes::{Hash, Proof, Value, C, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE},
    circuits::common::ValueTarget,
    primitives::falcon::{
        hash_to_point::RATE_RANGE, FALCON_ENCODING_BITS, MODULUS, N, NONCE_ELEMENTS,
    },
};

// MAX_Q < floor( |F| / p )
const P: u64 = MODULUS as u64; 
const MAX_Q: u64 = F::ORDER / MODULUS as u64; // TODO review that is floor(F::O/M)
const FALCON_ENCODING_BITS_usize: usize = FALCON_ENCODING_BITS as usize;

/// An element in the Falcon-512 field, ie. modulus 12289.
#[derive(Debug, Copy, Clone)]
pub struct FalconFTarget(Target);
impl FalconFTarget {
    /// Checks that r = x%p.
    /// Note: this gadget takes 11 plonky2 gates. // WIP: iterate it to use less gates.
    // That is, want: r = v % p (where p is the Falcon prime)
    // thus, it exists q s.th. v = q * p + r.
    // Range checks:
    // i) r < p
    // ii) q < floor(|F|/p) (|F|=Goldilocks prime)
    pub fn modulus(builder: &mut CircuitBuilder<F, D>, v: Target) -> Target {
        let q = builder.add_virtual_target();
        let r = builder.add_virtual_target();

        // assign the q & r values
            builder.add_simple_generator(FalconHintGenerator { v, q, r });


        let p = builder.constant(F::from_canonical_u64(MODULUS as u64));
        let computed_v = builder.mul_add(q, p, r);
        builder.connect(v, computed_v);

        // i) r < p
        assert_less::<FALCON_ENCODING_BITS_usize>(builder, r, p);
        // ii) q < MAX_Q
        let max_q = builder.constant(F::from_canonical_u64(MAX_Q));
        assert_less::<{ F::BITS }>(builder, q, max_q);

        r
    }
}

// v = q * p + r
#[derive(Debug, Default)]
struct FalconHintGenerator {
    v: Target,
    q: Target,
    r: Target,
}
impl SimpleGenerator<F, D> for FalconHintGenerator {
    fn id(&self) -> String {
        "FalconHintGenerator".to_string()
    }
    fn dependencies(&self) -> Vec<Target> {
        vec![self.v]
    }
    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let v = witness.get_target(self.v);
        let v64 = v.to_canonical_u64();
        let q64 = v64 / P;
        let r64 = v64 % P;

        out_buffer.set_target(self.q, F::from_canonical_u64(q64))?;
        out_buffer.set_target(self.r, F::from_canonical_u64(r64))?;

        Ok(())
    }
    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<()> {
        dst.write_target(self.v)?;
        dst.write_target(self.q)?;
        dst.write_target(self.r)?;
        Ok(())
    }
    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        let v = src.read_target()?;
        let q = src.read_target()?;
        let r = src.read_target()?;
        Ok(Self { v, q, r })
    }
}

// TODO move it to backends/plonky2/circuit/common.rs (not yet to avoid git-conflicts)
/// assert x<y
pub fn assert_less<const NUM_BITS: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: Target,
    y: Target,
) {
    // check that targets fit within `NUM_BITS` bits.
    builder.range_check(x, NUM_BITS);
    builder.range_check(y, NUM_BITS);
    // check that `y-(x+1)` fits within `NUM_BITS` bits.
    let x_plus_1 = builder.add_const(x, F::ONE);
    let expr = builder.sub(y, x_plus_1);
    builder.range_check(expr, NUM_BITS);
}

/// in Z_p[x]/(phi).
#[derive(Copy, Clone)]
pub struct PolynomialTarget {
    // pub coeffs: [FalconFTarget; N],
    pub coeffs: [Target; N],
}

pub struct SignatureVerifyGadget {}

/// Note: this gadget takes 4879 gates. // WIP: do a modified (cheaper) version.
fn hash_to_point_gadget(
    builder: &mut CircuitBuilder<F, D>,
    message: ValueTarget,
    nonce_elems: [Target; NONCE_ELEMENTS],
) -> Result<PolynomialTarget> {
    let mut state: [Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH] =
        [builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];

    for (&n, s) in nonce_elems.iter().zip(state.iter_mut()) {
        *s = n;
    }
    let perm_in = PlonkyPermutation::new(state);
    let perm_out = builder.permute::<PoseidonHash>(perm_in);
    let mut state: [Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH] = [builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];
    state[..].copy_from_slice(perm_out.as_ref());

    for (&m, s) in message.elements.iter().zip(state[RATE_RANGE].iter_mut()) {
        *s = m;
    }
    
    let mut i = 0;
    let mut res = [builder.zero(); N];
    let mut states: [[Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH]; 512+1] = [[builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];512+1];
    states[0][..].copy_from_slice(&state);
    for j in 0..64 {
        let perm_in = PlonkyPermutation::new(states[j]);
        let perm_out = builder.permute::<PoseidonHash>(perm_in);
        states[j+1][..].copy_from_slice(perm_out.as_ref());

        for a in &states[j+1][RATE_RANGE] {
            res[i] = FalconFTarget::modulus(builder, *a);
            i += 1;
        }
    }

    Ok(PolynomialTarget { coeffs: res })
}



#[cfg(test)]
pub mod tests {
    use std::ops::Div;

    use plonky2::{
        field::types::Field,
        hash::{
            hash_types::{HashOut, HashOutTarget},
            poseidon::PoseidonHash,
        },
        iop::{
            target::{BoolTarget, Target},
            witness::{PartialWitness, WitnessWrite},
        },
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::{
                CircuitConfig, CircuitData, ProverCircuitData, VerifierCircuitData,
                VerifierCircuitTarget,
            },
            config::Hasher,
            proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
        },
    };
    use rand::{rng, rngs::StdRng, Rng, RngCore, SeedableRng};

    use super::*;
    use crate::backends::plonky2::{
        basetypes::{Hash, F},
        circuits::common::CircuitBuilderPod,
        primitives::{
            falcon::{hash_to_point::hash_to_point, Nonce, SIG_NONCE_LEN},
            signature_proofbased::SecretKey,
        },
    };

    #[test]
    fn test_modulus() -> Result<()> {
        let p: F = F::from_canonical_u64(MODULUS as u64);
        let v: F = F::from_canonical_u64(p.0 * 42 + 3 as u64); // overflows p
        let r = F::from_canonical_u64(v.0 % p.0 as u64);
        let h = (v - r).div(p);
        assert_eq!(v, h * p + r);

        dbg!(&v);
        dbg!(&r);
        dbg!(&h);

        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let v_targ = builder.add_virtual_target();
        pw.set_target(v_targ, v)?;

        let r_targ = FalconFTarget::modulus(&mut builder, v_targ);
        dbg!(builder.num_gates());

        let expected_r_targ = builder.add_virtual_target();
        pw.set_target(expected_r_targ, r)?;
            builder.connect(r_targ, expected_r_targ);

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_hash_to_point() -> Result<()> {
        let mut rng = StdRng::from_os_rng();
        let mut nonce_bytes = [0u8; SIG_NONCE_LEN];
        rng.fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::new(nonce_bytes);
        let msg: Value = Value([F::ONE; 4]);
        let c = hash_to_point(msg, &nonce);
        assert!(c.coefficients.len() <= N);
        let coeffs_F: Vec<F> = c
            .coefficients
            .iter()
            .map(|e| F::from_canonical_u64(e.value() as u64))
            .collect();
        let mut c_padded = [F::ZERO; N];
        c_padded[..c.coefficients.len()].copy_from_slice(&coeffs_F);

        // circuit
        let config = CircuitConfig::standard_recursion_zk_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let msg_targ = builder.add_virtual_value();
        pw.set_target_arr(&msg_targ.elements, &msg.0)?;
        let nonce_targ = builder.add_virtual_target_arr::<NONCE_ELEMENTS>();
        pw.set_target_arr(&nonce_targ, &nonce.to_elements())?;

        let expected_c_targ = builder.add_virtual_target_arr::<N>();
        pw.set_target_arr(&expected_c_targ, &c_padded)?;

        let c_targ = hash_to_point_gadget(&mut builder, msg_targ, nonce_targ)?;
        for i in 0..N {
            builder.connect(c_targ.coeffs[i], expected_c_targ[i]);
        }

        dbg!(builder.num_gates());

        Ok(())
    }
}
