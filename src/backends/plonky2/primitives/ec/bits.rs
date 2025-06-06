use std::{array, marker::PhantomData};

use num::BigUint;
use plonky2::{
    field::{
        extension::Extendable,
        goldilocks_field::GoldilocksField,
        types::{Field, Field64},
    },
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData},
    util::serialization::{IoResult, Read, Write},
};

use crate::backends::plonky2::basetypes::{D, F};

#[derive(Debug)]
struct ConditionalZeroGenerator<F: RichField + Extendable<D>, const D: usize> {
    if_zero: Target,
    then_zero: Target,
    quot: Target,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D>
    for ConditionalZeroGenerator<F, D>
{
    fn id(&self) -> String {
        "ConditionalZeroGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![self.if_zero, self.then_zero]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let if_zero = witness.get_target(self.if_zero);
        let then_zero = witness.get_target(self.then_zero);
        if if_zero.is_zero() {
            out_buffer.set_target(self.quot, F::ZERO)?;
        } else {
            out_buffer.set_target(self.quot, then_zero / if_zero)?;
        }

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target(self.if_zero)?;
        dst.write_target(self.then_zero)?;
        dst.write_target(self.quot)
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            if_zero: src.read_target()?,
            then_zero: src.read_target()?,
            quot: src.read_target()?,
            _phantom: PhantomData,
        })
    }
}

/// A big integer, represented in base `2^32` with 10 digits, in little endian
/// form.
#[derive(Clone, Debug)]
pub struct BigUInt320Target(pub(super) [Target; 10]);

pub trait CircuitBuilderBits {
    /// Enforces the constraint that `then_zero` must be zero if `if_zero`
    /// is zero.
    ///
    /// The prover is required to exhibit a solution to the equation
    /// `if_zero * x == then_zero`.  If both `if_zero` and `then_zero`
    /// are zero, then it chooses the solution `x = 0`.
    fn conditional_zero(&mut self, if_zero: Target, then_zero: Target);

    /// Returns the binary representation of the target, in little-endian order.
    fn biguint_bits(&mut self, x: &BigUInt320Target) -> [BoolTarget; 320];

    /// Decomposes the target x as `y + 2^32 z`, where `0 < y,z < 2**32`, and
    /// `y=0` if `z=2**32-1`.  Note that calling [`CircuitBuilder::split_le`]
    /// with `num_bits = 64` will not check the latter condition.
    fn split_32_bit(&mut self, x: Target) -> [Target; 2];

    /// Interprets `arr` as an integer in base `[GoldilocksField::ORDER]`,
    /// with the digits in little endian order.  The length of `arr` must be at
    /// most 5.
    fn field_elements_to_biguint(&mut self, arr: &[Target]) -> BigUInt320Target;

    fn normalize_bigint(
        &mut self,
        x: &BigUInt320Target,
        max_digit_bits: usize,
        max_num_carries: usize,
    ) -> BigUInt320Target;

    fn constant_biguint320(&mut self, n: &BigUint) -> BigUInt320Target;
    fn add_virtual_biguint320_target(&mut self) -> BigUInt320Target;
    fn connect_biguint320(&mut self, x: &BigUInt320Target, y: &BigUInt320Target);
}

impl CircuitBuilderBits for CircuitBuilder<GoldilocksField, 2> {
    fn conditional_zero(&mut self, if_zero: Target, then_zero: Target) {
        let quot = self.add_virtual_target();
        self.add_simple_generator(ConditionalZeroGenerator {
            if_zero,
            then_zero,
            quot,
            _phantom: PhantomData,
        });
        let prod = self.mul(if_zero, quot);
        self.connect(prod, then_zero);
    }

    fn biguint_bits(&mut self, x: &BigUInt320Target) -> [BoolTarget; 320] {
        let bits = x.0.map(|t| self.low_bits(t, 32, 32));
        array::from_fn(|i| bits[i / 32][i % 32])
    }

    fn field_elements_to_biguint(&mut self, arr: &[Target]) -> BigUInt320Target {
        assert!(arr.len() <= 5);
        let zero = self.zero();
        let neg_one = self.neg_one();
        let two_32 = self.constant(GoldilocksField::from_canonical_u64(1 << 32));
        // Apply Horner's method to Σarr[i]*p^i.
        // First map each target to its limbs.
        let arr_limbs: Vec<_> = arr.iter().map(|x| self.split_32_bit(*x).to_vec()).collect();
        let res_limbs = arr_limbs
            .into_iter()
            .rev()
            .enumerate()
            .reduce(|(_, res), (i, a)| {
                // Compute p*res in unnormalised form, where each
                // coefficient is offset so as to ensure none (except
                // possibly the last) underflow.
                let prod = (0..=(2 * i + 1))
                    .map(|j| {
                        if j == 0 {
                            // x_0
                            res[0]
                        } else if j == 1 {
                            // x_1 - x_0 + 2^32
                            let diff = self.sub(res[1], res[0]);
                            self.add(diff, two_32)
                        } else if j < 2 * i {
                            // x_j + x_{j-2} - x_{j-1} + 2^32 - 1
                            let diff = self.sub(res[j], res[j - 1]);
                            let sum = self.add(diff, res[j - 2]);
                            let sum = self.add(sum, two_32);
                            self.add(sum, neg_one)
                        } else if j == 2 * i {
                            // x_{2*j - 2} - x_{2*j - 1} + 2^32
                            let diff = self.sub(res[2 * i - 2], res[2 * i - 1]);
                            let sum = self.add(diff, two_32);
                            self.add(sum, neg_one)
                        } else {
                            // x_{2*i - 1} - 1
                            self.add(res[2 * i - 1], neg_one)
                        }
                    })
                    .collect::<Vec<_>>();
                // Add arr[i].
                let prod_plus_lot = prod
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| match i {
                        0 => self.add(a[0], x),
                        1 => self.add(a[1], x),
                        _ => x,
                    })
                    .collect::<Vec<_>>();
                // Normalise.
                (
                    i,
                    normalize_biguint_limbs(self, &prod_plus_lot, 34, 2 * i + 1),
                )
            })
            .map(|(_, v)| v)
            .unwrap_or(vec![]);
        // Collect limbs, padding with 0s if necessary.
        BigUInt320Target(array::from_fn(|i| {
            if i < res_limbs.len() {
                res_limbs[i]
            } else {
                zero
            }
        }))
    }

    fn normalize_bigint(
        &mut self,
        x: &BigUInt320Target,
        max_digit_bits: usize,
        max_num_carries: usize,
    ) -> BigUInt320Target {
        let mut x = x.clone();
        for i in 0..max_num_carries {
            let (low, high) = self.split_low_high(x.0[i], 32, max_digit_bits);
            x.0[i] = low;
            x.0[i + 1] = self.add(x.0[i + 1], high);
        }
        x
    }

    fn split_32_bit(&mut self, x: Target) -> [Target; 2] {
        let (low, high) = self.split_low_high(x, 32, 64);
        let max = self.constant(GoldilocksField::from_canonical_i64(0xFFFFFFFF));
        let high_minus_max = self.sub(high, max);
        self.conditional_zero(high_minus_max, low);
        [low, high]
    }

    fn constant_biguint320(&mut self, n: &BigUint) -> BigUInt320Target {
        assert!(n.bits() <= 320);
        let digits = n.to_u32_digits();
        let targets = array::from_fn(|i| {
            let d = digits.get(i).copied().unwrap_or(0);
            self.constant(GoldilocksField::from_canonical_u32(d))
        });
        BigUInt320Target(targets)
    }

    fn add_virtual_biguint320_target(&mut self) -> BigUInt320Target {
        let targets = self.add_virtual_target_arr();
        for t in targets {
            self.range_check(t, 32);
        }
        BigUInt320Target(targets)
    }

    fn connect_biguint320(&mut self, x: &BigUInt320Target, y: &BigUInt320Target) {
        for i in 0..10 {
            self.connect(x.0[i], y.0[i]);
        }
    }
}

/// Normalises the limbs of a biguint assuming no overflow in the
/// field.
fn normalize_biguint_limbs(
    builder: &mut CircuitBuilder<F, D>,
    x: &[Target],
    max_digit_bits: usize,
    max_num_carries: usize,
) -> Vec<Target> {
    let mut x = x.to_vec();
    for i in 0..max_num_carries {
        let (low, high) = builder.split_low_high(x[i], 32, max_digit_bits);
        x[i] = low;
        x[i + 1] = builder.add(x[i + 1], high);
    }
    x
}
