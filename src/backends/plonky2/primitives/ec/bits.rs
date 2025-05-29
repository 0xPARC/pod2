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
        x: &mut BigUInt320Target,
        max_digit_bits: usize,
        max_num_digits: usize,
    );

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
        let mut ans = BigUInt320Target(array::from_fn(|_| self.zero()));
        let neg_one = self.neg_one();
        let two_32 = self.constant(GoldilocksField::from_canonical_u64(1 << 32));
        for (n, &x) in arr.iter().rev().enumerate() {
            // multiply by the order of the Goldilocks field
            for i in (0..(2 * n)).rev() {
                let tmp = self.add(ans.0[i + 1], two_32);
                ans.0[i + 1] = self.sub(tmp, ans.0[i]);
                let tmp = self.add(ans.0[i + 2], ans.0[i]);
                ans.0[i + 2] = self.add(tmp, neg_one);
            }
            // add x
            let [low, high] = self.split_32_bit(x);
            ans.0[0] = self.add(ans.0[0], low);
            ans.0[1] = self.add(ans.0[1], high);
            self.normalize_bigint(&mut ans, 34, 2 * n + 1);
        }
        ans
    }

    fn normalize_bigint(
        &mut self,
        x: &mut BigUInt320Target,
        max_digit_bits: usize,
        max_num_carries: usize,
    ) {
        for i in 0..max_num_carries {
            let (low, high) = self.split_low_high(x.0[i], 32, max_digit_bits);
            x.0[i] = low;
            x.0[i + 1] = self.add(x.0[i + 1], high);
        }
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
