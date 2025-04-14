//! This file implements the Plonky2 circuit which verifies the Falcon signatures
//! (https://falcon-sign.info). Compatible with the signatures generated by signature.rs.

use anyhow::Result;
use num::Zero;
use plonky2::{
    field::{
        extension::Extendable,
        types::{Field, Field64, PrimeField64},
    },
    gates::lookup_table::LookupTable,
    hash::{
        hash_types::{HashOut, HashOutTarget, RichField},
        hashing::PlonkyPermutation,
        poseidon::{Poseidon, PoseidonHash, PoseidonPermutation},
    },
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartialWitness, PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData, VerifierCircuitData,
            VerifierCircuitTarget,
        },
        config::{AlgebraicHasher, Hasher},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};

use crate::backends::plonky2::{
    basetypes::{Hash, Proof, Value, C, D, EMPTY_HASH, EMPTY_VALUE, F, VALUE_SIZE},
    circuits::common::{CircuitBuilderPod, ValueTarget},
    primitives::signature::falcon_lib::{
        hash_to_point::{hash_to_point, hash_to_point_no_mod, RATE_RANGE},
        math::{FalconFelt, FastFft, Polynomial},
        Signature, FALCON_ENCODING_BITS, MODULUS, N, NONCE_ELEMENTS,
    },
};

// MAX_Q < floor( |F| / p )
const P: u64 = MODULUS as u64;
const MAX_Q: u64 = F::ORDER / MODULUS as u64; // TODO review that is floor(F::O/M)
const FALCON_ENCODING_BITS_usize: usize = FALCON_ENCODING_BITS as usize;

pub trait CircuitBuilderFalcon<F: RichField + Extendable<D>, const D: usize> {
    fn add_virtual_polynomial<const DEG: usize>(&mut self) -> PolynomialTarget<DEG>;
}

impl CircuitBuilderFalcon<F, D> for CircuitBuilder<F, D> {
    fn add_virtual_polynomial<const DEG: usize>(&mut self) -> PolynomialTarget<DEG> {
        PolynomialTarget::<DEG>(self.add_virtual_target_arr())
    }
}

fn gen_falcon_field_table() -> LookupTable {
    let mut t: Vec<(u16, u16)> = vec![];
    for i in 0..MODULUS {
        t.push((i as u16, i as u16));
    }
    std::sync::Arc::new(t)
}

// TODO maybe abstract it from the concrete field, and move it to
// backends/plonky2/circuit/common.rs (not yet to avoid git-conflicts)
/// An element in the Falcon-512 field, ie. modulus 12289.
#[derive(Debug, Copy, Clone)]
pub struct FalconFTarget(Target);
impl FalconFTarget {
    /// Checks that r = x%p.
    /// Note: this gadget takes 11 plonky2 gates. // WIP: iterate it to use less gates.
    // That is, want: r = v % p (where p is the Falcon prime)
    // thus, it exists q s.th. v = q * p + r.
    // Range checks:
    // i) r < p (done through lookup)
    // ii) q < floor(|F|/p) (|F|=Goldilocks prime)
    pub fn modulus(builder: &mut CircuitBuilder<F, D>, falcon_lut_i: usize, v: Target) -> Target {
        let q = builder.add_virtual_target();
        let r = builder.add_virtual_target();

        // assign the q & r values
        builder.add_simple_generator(FalconHintGenerator { v, q, r });

        let p = builder.constant(F::from_canonical_u64(MODULUS as u64));
        let computed_v = builder.mul_add(q, p, r);
        builder.connect(v, computed_v);

        // i) r < p
        // assert_less::<FALCON_ENCODING_BITS_usize>(builder, r, p); // done with lookup // TODO rm line
        let lut_out = builder.add_lookup_from_index(r, falcon_lut_i);
        builder.connect(lut_out, r);
        // ii) q < MAX_Q
        let max_q = builder.constant(F::from_canonical_u64(MAX_Q));
        assert_less::<{ F::BITS }>(builder, q, max_q);

        r
    }
}

// TODO move it to backends/plonky2/circuit/common.rs (not yet to avoid git-conflicts)
/// Witness hint generator for reducing the Falcon modulus. v = q * p + r
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
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
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

/// PolynomialTarget represents an element in Z_p[x]/(phi) inside a circuit.
/// This data type is only for polynomimals at the Falcon-512 field 12289
/// represented over the Goldilocks field.
/// Notice that the coefficients are not represented as Falcon
/// field elements but as Target, ie. Goldilocks field elements in-circuit.
#[derive(Copy, Clone)]
pub struct PolynomialTarget<const DEG: usize>([Target; DEG]);

impl<const DEG: usize> PolynomialTarget<DEG> {
    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        p: &Polynomial<FalconFelt>,
    ) -> Result<()> {
        // padd the poly coeffs to DEG
        let mut coeffs = p.to_elements();
        coeffs.resize(DEG, F::ZERO);
        pw.set_target_arr(&self.0, &coeffs)?;
        Ok(())
    }
    pub fn set_targets_not_reduced_q(
        &self,
        pw: &mut PartialWitness<F>,
        p: &Polynomial<FalconFelt>,
    ) -> Result<()> {
        // padd the poly coeffs to DEG
        let mut coeffs = p.to_elements();
        coeffs.resize(DEG, F::ZERO);
        pw.set_target_arr(&self.0, &coeffs)?;
        Ok(())
    }

    pub fn evaluate(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        falcon_lut_i: usize,
        x: Target,
    ) -> Target {
        let coeffs = self.0;

        // We want to compute
        // res = c_0 + x * c_1 + x^2 * c_2 + x^3 * c_3 + ... + x^{n-2} * c_{n-2} + x^{n-1} * c_{n-1}
        // so in order to do it more efficiently (less constraints) we do
        // res = (((c_{n-1} * x + c_{n-2}) * x + c_{n-3})... ) * x + c_0
        let mut res: Target = coeffs[DEG - 1];
        for i in (0..DEG - 1).rev() {
            res = builder.mul_add(res, x, coeffs[i]);
            // Since Goldilocks:64 bits and Falcon field:14 bits, we can
            // multiply 4 Falcon field elements together without overflowing the
            // Goldilocks field. We're also doing additions, therefore, reduce
            // modulus only one every Y iterations:
            const Y: usize = 3;
            if i % Y == 0 {
                res = FalconFTarget::modulus(builder, falcon_lut_i, res);
            }
        }
        res
    }

    pub fn modulo_reduce(&self, builder: &mut CircuitBuilder<F, D>, falcon_lut_i: usize) -> Self {
        Self(std::array::from_fn(|i| {
            FalconFTarget::modulus(builder, falcon_lut_i, self.0[i])
        }))
    }
}

pub struct SignatureVerifyGadget {
    enabled: BoolTarget,
    msg: ValueTarget,
    tau: Target,
    pk: PolynomialTarget<N>,
    s1: PolynomialTarget<N>,
    s2: PolynomialTarget<N>,
    s2h: PolynomialTarget<{ N * 2 }>, // claimed to be s2*h
    nonce_elems: [Target; NONCE_ELEMENTS],
}

impl SignatureVerifyGadget {
    pub fn build(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let enabled = builder.add_virtual_bool_target_safe();

        let tau = builder.add_virtual_target();
        // TODO assert that tau!={1,0,-1}

        let pk = builder.add_virtual_polynomial::<N>();
        let s1 = builder.add_virtual_polynomial::<N>();
        let s2 = builder.add_virtual_polynomial::<N>();
        // let h = PolynomialTarget(builder.add_virtual_target_arr::<N>()); // =pk
        let s2h = builder.add_virtual_polynomial::<{ N * 2 }>();

        let msg = builder.add_virtual_value();
        let nonce_elems = builder.add_virtual_target_arr::<NONCE_ELEMENTS>();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        let c = hash_to_point_gadget(builder, falcon_lut_i, true, msg, nonce_elems)?;

        equality_check(builder, falcon_lut_i, enabled, tau, s1, s2, pk, s2h, c)?;

        // norm check
        // TODO

        Ok(Self {
            enabled,
            msg,
            tau,
            pk,
            s1,
            s2,
            s2h,
            nonce_elems,
        })
    }

    pub fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        enabled: bool,
        tau: FalconFelt,
        pk: Polynomial<FalconFelt>,
        msg: Value,
        sig: Signature,
    ) -> Result<()> {
        pw.set_bool_target(self.enabled, enabled)?;
        self.msg.set_targets(pw, &msg)?;
        pw.set_target(self.tau, F::from_canonical_u64(tau.value() as u64))?;
        self.pk.set_targets(pw, &pk)?;
        self.s2.set_targets(pw, &sig.s2.0)?;
        pw.set_target_arr(&self.nonce_elems, &sig.nonce.to_elements())?;

        let s2h = polynomial_mul_modulo_p(&sig.s2.0, &pk);
        self.s2h.set_targets_not_reduced_q(pw, &s2h)?;

        // let s2h_u64: [u64; N * 2] = std::array::from_fn(|i| s2h.coefficients[i].0 as u64);
        // let s2h_reduced = Polynomial::<FalconFelt>::reduce_negacyclic(&s2h_u64);

        // compute s1 to pass it as hint
        let c = hash_to_point(msg, &sig.nonce);
        // let c = hash_to_point_no_mod(msg, &sig.nonce);
        let s1 = (c.fft() - sig.s2.fft().hadamard_mul(&sig.pk_poly().fft())).ifft();
        // let s1 = c.clone() - s2h.clone();
        // let s1 = c.clone() - s2h_reduced.clone();
        self.s1.set_targets(pw, &s1)?;

        // sanity check
        #[cfg(test)]
        {
            // check product
            let s2_tau = sig.s2.evaluate(tau);
            let h_tau = pk.evaluate(tau);
            let s2h_tau = s2h.evaluate(tau);
            assert_eq!(s2_tau * h_tau, s2h_tau);

            // check sum
            let s1_tau = s1.evaluate(tau);
            let c_tau = c.evaluate(tau);
            // assert_eq!(s1_tau + s2h_tau, c_tau);
            // assert_eq!(s1_tau, c_tau - s2h_tau);
        }

        Ok(())
    }
}

/// Computes the probabilistic proof for s1 == c - s2 * h (mod q)
/// ==> s1 + s2*h == c
fn equality_check(
    builder: &mut CircuitBuilder<F, D>,
    falcon_lut_i: usize,
    enabled: BoolTarget,
    tau: Target,
    s1: PolynomialTarget<N>,
    s2: PolynomialTarget<N>,
    h: PolynomialTarget<N>,
    s2h: PolynomialTarget<{ 2 * N }>,
    // note `c` could be with mod q not applied to its coefficients (q=Falcon
    // prime)
    c: PolynomialTarget<N>,
) -> Result<()> {
    let s1_tau = s1.evaluate(builder, falcon_lut_i, tau);
    let s2_tau = s2.evaluate(builder, falcon_lut_i, tau);
    let c_tau = c.evaluate(builder, falcon_lut_i, tau);
    let h_tau = h.evaluate(builder, falcon_lut_i, tau);
    let s2h_tau = s2h.evaluate(builder, falcon_lut_i, tau);
    let zero = builder.zero();

    // polynomial probabilistic product
    let s2tau_htau_raw = builder.mul(s2_tau, h_tau);
    let s2tau_htau = FalconFTarget::modulus(builder, falcon_lut_i, s2tau_htau_raw);
    // here we could do only 1 select, and instead of using `zero` using the
    // other value (s2tau_htau), but the code could be more confusing while only
    // saving a single gate
    let rhs = builder.select(enabled, s2h_tau, zero);
    let lhs = builder.select(enabled, s2tau_htau, zero);
    builder.connect(lhs, rhs);

    // check s1(tau) + s2(tau) * h(tau) == c(tau)
    let s1s2h_raw = builder.add(s1_tau, s2tau_htau);
    let s1s2h = FalconFTarget::modulus(builder, falcon_lut_i, s1s2h_raw);
    // builder.connect(lhs, c_tau); // TODO dependent on 'enabled'
    // TODO-NOTE: maybe don't do the full `s1(tau)+s2(tau)h(tau)-c(tau)==0`, and
    // just compute the actual s1(x) polynomial, so that then the norm can be
    // computed from it.

    Ok(())
}

/// compatible with falcon/hash_to_point.rs#hash_to_point
fn hash_to_point_gadget(
    builder: &mut CircuitBuilder<F, D>,
    falcon_lut_i: usize,
    apply_mod: bool,
    message: ValueTarget,
    nonce_elems: [Target; NONCE_ELEMENTS],
) -> Result<PolynomialTarget<N>> {
    let mut state: [Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH] =
        [builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];

    for (&n, s) in nonce_elems.iter().zip(state.iter_mut()) {
        *s = n;
    }
    let perm_in = PlonkyPermutation::new(state);
    let perm_out = builder.permute::<PoseidonHash>(perm_in);
    let mut state: [Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH] =
        [builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH];
    state[..].copy_from_slice(perm_out.as_ref());

    for (&m, s) in message.elements.iter().zip(state[RATE_RANGE].iter_mut()) {
        *s = m;
    }

    let mut i = 0;
    let mut res = [builder.zero(); N];
    let mut states: [[Target; <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH]; 512 + 1] =
        [[builder.zero(); <PoseidonPermutation<F> as PlonkyPermutation<F>>::WIDTH]; 512 + 1];
    states[0][..].copy_from_slice(&state);
    for j in 0..64 {
        let perm_in = PlonkyPermutation::new(states[j]);
        let perm_out = builder.permute::<PoseidonHash>(perm_in);
        states[j + 1][..].copy_from_slice(perm_out.as_ref());

        for a in &states[j + 1][RATE_RANGE] {
            res[i] = if apply_mod {
                FalconFTarget::modulus(builder, falcon_lut_i, *a)
            } else {
                *a
            };
            i += 1;
        }
    }

    Ok(PolynomialTarget(res))
}

// Return a(x) * b(x) over Z_p[x], without reducing modulo phi, ie. not over
// Z_p[x]/(X^N+1).
// For the in-circuit equivalent logic, notice that the input polynomials are of
// degree N, and the ouptut polynomial is of degree 2N. Since N=512, Falcon
// field prime is 12289, and Goldilocks field prime is 2^64-2^32-1, the
// resulting polynomial coeffs will not overflow the Goldilocks field.
pub fn polynomial_mul_modulo_p(
    a: &Polynomial<FalconFelt>,
    b: &Polynomial<FalconFelt>,
) -> Polynomial<FalconFelt> {
    let mut c = [FalconFelt::new(0); N * 2];
    for i in 0..N {
        for j in 0..N {
            if a.coefficients[i].is_zero() || b.coefficients[j].is_zero() {
                continue;
            } else {
                c[i + j] += a.coefficients[i] * b.coefficients[j];
            }
        }
    }
    Polynomial::<FalconFelt>::new(c.to_vec())
}

#[cfg(test)]
pub mod tests {
    use std::ops::Div;

    use plonky2::{
        field::types::{Field, Sample},
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
    use rand_chacha::ChaCha20Rng;

    use super::*;
    use crate::backends::plonky2::{
        basetypes::{Hash, F},
        circuits::common::CircuitBuilderPod,
        primitives::signature::falcon_lib::{
            hash_to_point::hash_to_point, Nonce, SecretKey, SIG_NONCE_LEN,
        },
    };

    #[test]
    fn test_falcon_field_table() -> Result<()> {
        let r = F::from_canonical_u64((MODULUS - 1) as u64);
        test_falcon_field_table_opt(r, true)?;

        let r = F::from_canonical_u64((MODULUS) as u64);
        test_falcon_field_table_opt(r, false)?;
        let r = F::from_canonical_u64((MODULUS + 1) as u64);
        test_falcon_field_table_opt(r, false)?;

        Ok(())
    }
    fn test_falcon_field_table_opt(r: F, expect_pass: bool) -> Result<()> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        let r_targ = builder.add_virtual_target();
        let lut_out = builder.add_lookup_from_index(r_targ, falcon_lut_i);
        builder.connect(lut_out, r_targ);

        pw.set_target(r_targ, r)?;

        // generate & verify proof
        let data = builder.build::<C>();
        if expect_pass {
            let proof = data.prove(pw)?;
            data.verify(proof.clone())?;
        } else {
            assert!(data.prove(pw).is_err()); // expect prove to fail
        }

        Ok(())
    }

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

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        let v_targ = builder.add_virtual_target();
        pw.set_target(v_targ, v)?;

        let r_targ = FalconFTarget::modulus(&mut builder, falcon_lut_i, v_targ);
        dbg!(builder.num_gates());

        let expected_r_targ = builder.add_virtual_target();
        pw.set_target(expected_r_targ, r)?;
        builder.connect(r_targ, expected_r_targ);

        dbg!(builder.num_gates());

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_polynomial_evaluate() -> Result<()> {
        let mut rng = StdRng::from_os_rng();

        let coeffs: Vec<FalconFelt> = std::iter::repeat_with(|| FalconFelt::new(rng.random()))
            .take(N)
            .collect();
        let p: Polynomial<FalconFelt> = Polynomial::new(coeffs);

        let x = FalconFelt::new(rng.random());
        let eval = p.evaluate(x);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        // set targets
        let p_targ = builder.add_virtual_polynomial::<N>();
        p_targ.set_targets(&mut pw, &p)?;
        let x_targ = builder.add_virtual_target();
        pw.set_target(x_targ, F::from_canonical_u64(x.value() as u64))?;
        let expected_eval_targ = builder.add_virtual_target();
        pw.set_target(
            expected_eval_targ,
            F::from_canonical_u64(eval.value() as u64),
        )?;

        let eval_targ: Target = p_targ.evaluate(&mut builder, falcon_lut_i, x_targ);
        builder.connect(eval_targ, expected_eval_targ);

        dbg!(builder.num_gates());

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_poly_probabilistic_mul() -> Result<()> {
        let seed = [0_u8; 32];
        let mut rng = ChaCha20Rng::from_seed(seed);

        let coeffs: Vec<FalconFelt> = std::iter::repeat_with(|| FalconFelt::new(rng.random()))
            .take(N)
            .collect();
        let f: Polynomial<FalconFelt> = Polynomial::new(coeffs);
        let coeffs: Vec<FalconFelt> = std::iter::repeat_with(|| FalconFelt::new(rng.random()))
            .take(N)
            .collect();
        let h: Polynomial<FalconFelt> = Polynomial::new(coeffs);

        let fh = polynomial_mul_modulo_p(&f, &h);

        let tau = FalconFelt::new(rng.random());

        let f_tau = f.evaluate(tau);
        let h_tau = h.evaluate(tau);
        let fh_tau = fh.evaluate(tau);
        // sanity check
        assert_eq!(f_tau * h_tau, fh_tau);

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        let f_targ = builder.add_virtual_polynomial::<N>();
        f_targ.set_targets(&mut pw, &f)?;
        let h_targ = builder.add_virtual_polynomial::<N>();
        h_targ.set_targets(&mut pw, &h)?;
        let fh_targ = builder.add_virtual_polynomial::<{ N * 2 }>();
        fh_targ.set_targets(&mut pw, &fh)?;
        let tau_targ = builder.add_virtual_target();
        pw.set_target(tau_targ, F::from_canonical_u64(tau.value() as u64))?;

        let f_tau_targ = f_targ.evaluate(&mut builder, falcon_lut_i, tau_targ);
        let h_tau_targ = h_targ.evaluate(&mut builder, falcon_lut_i, tau_targ);
        let fh_tau_targ = fh_targ.evaluate(&mut builder, falcon_lut_i, tau_targ);

        let ftau_htau_targ_raw = builder.mul(f_tau_targ, h_tau_targ);
        let ftau_htau_targ = FalconFTarget::modulus(&mut builder, falcon_lut_i, ftau_htau_targ_raw);
        builder.connect(ftau_htau_targ, fh_tau_targ);

        dbg!(builder.num_gates());

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
        let coeffs_f: Vec<F> = c
            .coefficients
            .iter()
            .map(|e| F::from_canonical_u64(e.value() as u64))
            .collect();
        let mut c_padded = [F::ZERO; N];
        c_padded[..c.coefficients.len()].copy_from_slice(&coeffs_f);

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let falcon_lut_i = builder.add_lookup_table_from_pairs(gen_falcon_field_table());

        let msg_targ = builder.add_virtual_value();
        pw.set_target_arr(&msg_targ.elements, &msg.0)?;
        let nonce_targ = builder.add_virtual_target_arr::<NONCE_ELEMENTS>();
        pw.set_target_arr(&nonce_targ, &nonce.to_elements())?;

        let expected_c_targ = builder.add_virtual_target_arr::<N>();
        pw.set_target_arr(&expected_c_targ, &c_padded)?;

        let c_targ = hash_to_point_gadget(&mut builder, falcon_lut_i, true, msg_targ, nonce_targ)?;
        for i in 0..N {
            builder.connect(c_targ.0[i], expected_c_targ[i]);
        }

        // apply_mod:true= 4879 gates,
        // apply_mod:false= 64 gates.
        dbg!(builder.num_gates());

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_falcon_gadget() -> Result<()> {
        let seed = [0_u8; 32];
        let mut rng = ChaCha20Rng::from_seed(seed);

        // generate random keys
        let sk = SecretKey::with_rng(&mut rng);
        let pk = sk.public_key();

        // sign a random message
        let msg: Value = Value([F::ONE; 4]);
        let sig = sk.sign_with_rng(msg, &mut rng);

        // make sure the signature verifies correctly
        assert!(pk.verify(msg, &sig));

        // let tau = F::rand();
        let tau = FalconFelt::new(rng.random());

        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let signature_targ = SignatureVerifyGadget::build(&mut builder)?;
        signature_targ.set_targets(&mut pw, true, tau, sig.pk_poly().0.clone(), msg, sig)?;

        // c no_mod = 9874 gates
        // c with mod = 14687 gates
        dbg!(builder.num_gates());

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }
}
