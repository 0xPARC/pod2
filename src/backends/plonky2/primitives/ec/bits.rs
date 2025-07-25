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
    util::serialization::{Buffer, IoResult, Read, Write},
};
use serde::{Deserialize, Serialize};

use crate::backends::plonky2::basetypes::{D, F};

#[derive(Debug, Default, Clone)]
pub(crate) struct ConditionalZeroGenerator<F: RichField + Extendable<D>, const D: usize> {
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
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BigUInt320Target {
    #[serde(with = "serde_arrays")]
    pub limbs: [Target; 10],
    #[serde(with = "serde_arrays")]
    pub bits: [BoolTarget; 320],
}

pub trait CircuitBuilderBits {
    /// Enforces the constraint that `then_zero` must be zero if `if_zero`
    /// is zero.
    ///
    /// The prover is required to exhibit a solution to the equation
    /// `if_zero * x == then_zero`.  If both `if_zero` and `then_zero`
    /// are zero, then it chooses the solution `x = 0`.
    fn conditional_zero(&mut self, if_zero: Target, then_zero: Target);

    /// Decomposes the target x as `y + 2^32 z`, where `0 < y,z < 2**32`, and
    /// `y=0` if `z=2**32-1`.  Note that calling [`CircuitBuilder::split_le`]
    /// with `num_bits = 64` will not check the latter condition.
    fn split_32_bit(&mut self, x: Target) -> [Target; 2];

    /// Like `split_low_high` except it doesn't discard the bit decompositions.
    fn split_low_high_with_bits(
        &mut self,
        x: Target,
        n_log: usize,
        num_bits: usize,
    ) -> ((Target, Vec<BoolTarget>), (Target, Vec<BoolTarget>));

    /// Interprets `arr` as an integer in base `[GoldilocksField::ORDER]`,
    /// with the digits in little endian order.  The length of `arr` must be at
    /// most 5.
    fn field_elements_to_biguint(&mut self, arr: &[Target]) -> BigUInt320Target;

    fn constant_biguint320(&mut self, n: &BigUint) -> BigUInt320Target;
    fn biguint320_target_from_limbs(&mut self, x: &[Target]) -> BigUInt320Target;
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

    fn field_elements_to_biguint(&mut self, arr: &[Target]) -> BigUInt320Target {
        assert!(arr.len() <= 5);
        let zero = self.zero();
        let neg_one = self.neg_one();
        let two_32 = self.constant(GoldilocksField::from_canonical_u64(1 << 32));
        // Apply Horner's method to Σarr[i]*p^i.
        // First map each target to its limbs.
        let arr_limbs: Vec<_> = arr
            .iter()
            .map(|x| (self.split_32_bit(*x).to_vec(), vec![]))
            .collect();
        let (res_limbs, res_bits) = arr_limbs
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
                            res.0[0]
                        } else if j == 1 {
                            // x_1 - x_0 + 2^32
                            let diff = self.sub(res.0[1], res.0[0]);
                            self.add(diff, two_32)
                        } else if j < 2 * i {
                            // x_j + x_{j-2} - x_{j-1} + 2^32 - 1
                            let diff = self.sub(res.0[j], res.0[j - 1]);
                            let sum = self.add(diff, res.0[j - 2]);
                            let sum = self.add(sum, two_32);
                            self.add(sum, neg_one)
                        } else if j == 2 * i {
                            // x_{2*j - 2} - x_{2*j - 1} + 2^32
                            let diff = self.sub(res.0[2 * i - 2], res.0[2 * i - 1]);
                            let sum = self.add(diff, two_32);
                            self.add(sum, neg_one)
                        } else {
                            // x_{2*i - 1} - 1
                            self.add(res.0[2 * i - 1], neg_one)
                        }
                    })
                    .collect::<Vec<_>>();
                // Add arr[i].
                let prod_plus_lot = prod
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| match i {
                        0 => self.add(a.0[0], x),
                        1 => self.add(a.0[1], x),
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
            .unwrap_or((vec![], vec![]));
        // Collect limbs, padding with 0s if necessary.
        let limbs: [Target; 10] = array::from_fn(|i| {
            if i < res_limbs.len() {
                res_limbs[i]
            } else {
                zero
            }
        });
        // Collect bits, padding with 0s if necessary.
        let bits: [BoolTarget; 320] = array::from_fn(|i| {
            if i < res_bits.len() {
                res_bits[i]
            } else {
                self._false()
            }
        });
        BigUInt320Target { limbs, bits }
    }

    fn split_32_bit(&mut self, x: Target) -> [Target; 2] {
        let (low, high) = self.split_low_high(x, 32, 64);
        let max = self.constant(GoldilocksField::from_canonical_i64(0xFFFFFFFF));
        let high_minus_max = self.sub(high, max);
        self.conditional_zero(high_minus_max, low);
        [low, high]
    }

    fn split_low_high_with_bits(
        &mut self,
        x: Target,
        n_log: usize,
        num_bits: usize,
    ) -> ((Target, Vec<BoolTarget>), (Target, Vec<BoolTarget>)) {
        let low = self.add_virtual_target();
        let high = self.add_virtual_target();

        self.add_simple_generator(LowHighGenerator {
            integer: x,
            n_log,
            low,
            high,
        });

        let low_bits = self.split_le(low, n_log);
        let high_bits = self.split_le(high, num_bits - n_log);

        let pow2 = self.constant(F::from_canonical_u64(1 << n_log));
        let comp_x = self.mul_add(high, pow2, low);
        self.connect(x, comp_x);

        ((low, low_bits), (high, high_bits))
    }

    fn constant_biguint320(&mut self, n: &BigUint) -> BigUInt320Target {
        assert!(n.bits() <= 320);
        let digits = n.to_u32_digits();
        let limbs: [Target; 10] = array::from_fn(|i| {
            let d = digits.get(i).copied().unwrap_or(0);
            self.constant(GoldilocksField::from_canonical_u32(d))
        });
        self.biguint320_target_from_limbs(&limbs)
    }

    fn biguint320_target_from_limbs(&mut self, x: &[Target]) -> BigUInt320Target {
        assert!(x.len() == 10);
        let limbs = array::from_fn(|i| x[i]);
        let bit_vec = biguint_limbs_to_bits(self, x);
        BigUInt320Target {
            limbs,
            bits: array::from_fn(|i| bit_vec[i]),
        }
    }

    fn add_virtual_biguint320_target(&mut self) -> BigUInt320Target {
        let limbs: [Target; 10] = self.add_virtual_target_arr();
        self.biguint320_target_from_limbs(&limbs)
    }

    fn connect_biguint320(&mut self, x: &BigUInt320Target, y: &BigUInt320Target) {
        for i in 0..10 {
            self.connect(x.limbs[i], y.limbs[i]);
        }
    }
}

/// Normalises the limbs of a biguint assuming no overflow in the
/// field. Returns the limbs together with their bit decomposition.
fn normalize_biguint_limbs(
    builder: &mut CircuitBuilder<F, D>,
    x: &[Target],
    max_digit_bits: usize,
    max_num_carries: usize,
) -> (Vec<Target>, Vec<BoolTarget>) {
    let mut x = x.to_vec();
    let mut bits = Vec::with_capacity(32 * (max_num_carries + 1));
    for i in 0..max_num_carries {
        let ((low, mut low_bits), (high, _)) =
            builder.split_low_high_with_bits(x[i], 32, max_digit_bits);
        x[i] = low;
        x[i + 1] = builder.add(x[i + 1], high);
        bits.append(&mut low_bits);
    }
    let mut final_bits = builder.split_le(x[max_num_carries], 32);
    bits.append(&mut final_bits);
    (x, bits)
}

/// Converts biguint limbs to bits, checking that each limb is 32-bits
/// long.
fn biguint_limbs_to_bits(builder: &mut CircuitBuilder<F, D>, limbs: &[Target]) -> Vec<BoolTarget> {
    limbs
        .iter()
        .flat_map(|t| builder.split_le(*t, 32))
        .collect()
}

/*
Copied from https://github.com/0xPolygonZero/plonky2/blob/82791c4809d6275682c34b926390ecdbdc2a5297/plonky2/src/gadgets/range_check.rs#L62
 */

#[derive(Debug, Default, Clone)]
pub struct LowHighGenerator {
    integer: Target,
    n_log: usize,
    low: Target,
    high: Target,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for LowHighGenerator {
    fn id(&self) -> String {
        "LowHighGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![self.integer]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let integer_value = witness.get_target(self.integer).to_canonical_u64();
        let low = integer_value & ((1 << self.n_log) - 1);
        let high = integer_value >> self.n_log;

        out_buffer.set_target(self.low, F::from_canonical_u64(low))?;
        out_buffer.set_target(self.high, F::from_canonical_u64(high))
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_target(self.integer)?;
        dst.write_usize(self.n_log)?;
        dst.write_target(self.low)?;
        dst.write_target(self.high)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let integer = src.read_target()?;
        let n_log = src.read_usize()?;
        let low = src.read_target()?;
        let high = src.read_target()?;
        Ok(Self {
            integer,
            n_log,
            low,
            high,
        })
    }
}
