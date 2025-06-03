//! Implementation of the elliptic curve ecGFp5.
//!
//! We roughly follow pornin/ecgfp5.
use core::ops::{Add, Mul};
use std::{
    ops::{AddAssign, Neg, Sub},
    sync::LazyLock,
};

use num::{bigint::BigUint, Num, One};
use plonky2::{
    field::{
        extension::{quintic::QuinticExtension, Extendable, FieldExtension},
        goldilocks_field::GoldilocksField,
        ops::Square,
        types::Field,
    },
    hash::poseidon::PoseidonHash,
    iop::{generator::SimpleGenerator, target::BoolTarget, witness::WitnessWrite},
    plonk::circuit_builder::CircuitBuilder,
    util::serialization::{Read, Write},
};
use serde::{Deserialize, Serialize};

use crate::backends::plonky2::{
    circuits::common::ValueTarget,
    primitives::ec::{
        bits::BigUInt320Target,
        field::{get_nnf_target, CircuitBuilderNNF, OEFTarget},
        gates::{curve::ECAddHomog, generic::SimpleGate},
    },
};

type ECField = QuinticExtension<GoldilocksField>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Point {
    pub x: ECField,
    pub u: ECField,
}

impl Point {
    pub fn as_fields(&self) -> Vec<crate::middleware::F> {
        self.x.0.iter().chain(self.u.0.iter()).cloned().collect()
    }
}

#[derive(Clone, Copy, Debug)]
struct HomogPoint {
    pub x: ECField,
    pub z: ECField,
    pub u: ECField,
    pub t: ECField,
}

pub(super) trait ECFieldExt<const D: usize>:
    Sized
    + Copy
    + Mul<Self, Output = Self>
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Neg<Output = Self>
{
    type Base: FieldExtension<D, BaseField = GoldilocksField>;

    fn to_base(self) -> [Self::Base; 5];
    fn from_base(components: [Self::Base; 5]) -> Self;

    fn mul_field_gen(self, factor: u32) -> Self {
        let in_arr = self.to_base();
        let field_factor = GoldilocksField::from_canonical_u32(factor);
        let field_factor_norm = GoldilocksField::from_canonical_u32(3 * factor);
        let out_arr = [
            in_arr[4].scalar_mul(field_factor_norm),
            in_arr[0].scalar_mul(field_factor),
            in_arr[1].scalar_mul(field_factor),
            in_arr[2].scalar_mul(field_factor),
            in_arr[3].scalar_mul(field_factor),
        ];
        Self::from_base(out_arr)
    }

    fn add_field_gen(self, factor: GoldilocksField) -> Self {
        let mut b1 = self.to_base();
        let mut b2 = b1[1].to_basefield_array();
        b2[0] += factor;
        b1[1] = Self::Base::from_basefield_array(b2);
        Self::from_base(b1)
    }

    fn add_scalar(self, scalar: GoldilocksField) -> Self {
        let mut b1 = self.to_base();
        let mut b2 = b1[0].to_basefield_array();
        b2[0] += scalar;
        b1[0] = Self::Base::from_basefield_array(b2);
        Self::from_base(b1)
    }

    fn double(self) -> Self {
        self + self
    }
}

impl ECFieldExt<1> for ECField {
    type Base = GoldilocksField;
    fn to_base(self) -> [Self::Base; 5] {
        self.to_basefield_array()
    }
    fn from_base(components: [Self::Base; 5]) -> Self {
        Self::from_basefield_array(components)
    }
}

pub(super) fn add_homog<const D: usize, F: ECFieldExt<D>>(x1: F, u1: F, x2: F, u2: F) -> [F; 4] {
    let t1 = x1 * x2;
    let t3 = u1 * u2;
    let t5 = x1 + x2;
    let t6 = u1 + u2;
    let t7 = t1.add_field_gen(Point::B1);
    let t9 = t3 * (t5.mul_field_gen(2 * Point::B1_U32) + t7.double());
    let t10 = t3.double().add_scalar(GoldilocksField::ONE) * (t5 + t7);
    let x = (t10 - t7).mul_field_gen(Point::B1_U32);
    let z = t7 - t9;
    let u = t6 * (-t1).add_field_gen(Point::B1);
    let t = t7 + t9;
    [x, z, u, t]
}

// See CircuitBuilderEllptic::add_point for an explanation of why we need this function.
// cf. https://github.com/pornin/ecgfp5/blob/ce059c6d1e1662db437aecbf3db6bb67fe63c716/rust/src/curve.rs#L157
pub(super) fn add_homog_offset<const D: usize, F: ECFieldExt<D>>(
    x1: F,
    u1: F,
    x2: F,
    u2: F,
) -> [F; 4] {
    let t1 = x1 * x2;
    let t3 = u1 * u2;
    let t5 = x1 + x2;
    let t6 = u1 + u2;
    let t7 = t1.add_field_gen(Point::B1);
    let t9 = t3 * (t5.mul_field_gen(2 * Point::B1_U32) + t7.double());
    let t10 = t3.double().add_scalar(GoldilocksField::ONE) * (t5 + t7);
    let x = (t10 - t7).mul_field_gen(Point::B1_U32);
    let z = t1 - t9;
    let u = t6 * (-t1).add_field_gen(Point::B1);
    let t = t1 + t9;
    [x, z, u, t]
}

const GROUP_ORDER_STR: &str = "1067993516717146951041484916571792702745057740581727230159139685185762082554198619328292418486241";
pub static GROUP_ORDER: LazyLock<BigUint> =
    LazyLock::new(|| BigUint::from_str_radix(GROUP_ORDER_STR, 10).unwrap());

static FIELD_NUM_SQUARES: LazyLock<BigUint> =
    LazyLock::new(|| (ECField::order() - BigUint::one()) >> 1);

static GROUP_ORDER_HALF_ROUND_UP: LazyLock<BigUint> =
    LazyLock::new(|| (&*GROUP_ORDER + BigUint::one()) >> 1);

impl Point {
    const B1_U32: u32 = 263;
    const B1: GoldilocksField = GoldilocksField(Self::B1_U32 as u64);

    pub fn b() -> ECField {
        ECField::from_basefield_array([
            GoldilocksField::ZERO,
            Self::B1,
            GoldilocksField::ZERO,
            GoldilocksField::ZERO,
            GoldilocksField::ZERO,
        ])
    }

    const ZERO: Self = Self {
        x: ECField::ZERO,
        u: ECField::ZERO,
    };

    pub fn generator() -> Self {
        Self {
            x: ECField::from_basefield_array([
                GoldilocksField::from_canonical_u64(12883135586176881569),
                GoldilocksField::from_canonical_u64(4356519642755055268),
                GoldilocksField::from_canonical_u64(5248930565894896907),
                GoldilocksField::from_canonical_u64(2165973894480315022),
                GoldilocksField::from_canonical_u64(2448410071095648785),
            ]),
            u: ECField::from_canonical_u64(13835058052060938241),
        }
    }

    fn add_homog(self, rhs: Point) -> HomogPoint {
        let [x, z, u, t] = add_homog(self.x, self.u, rhs.x, rhs.u);
        HomogPoint { x, z, u, t }
    }

    fn double_homog(self) -> HomogPoint {
        self.add_homog(self)
        /*
        let [x, z, u, t] = double_homog(self.x, self.u);
        HomogPoint { x, z, u, t }
        */
    }

    pub fn double(self) -> Self {
        self.double_homog().into()
    }

    pub fn inverse(self) -> Self {
        Self {
            x: self.x,
            u: -self.u,
        }
    }

    pub fn is_zero(self) -> bool {
        self.x.is_zero() && self.u.is_zero()
    }

    pub fn is_on_curve(self) -> bool {
        self.x == self.u.square() * (self.x * (self.x + ECField::TWO) + Self::b())
    }

    pub fn is_in_subgroup(self) -> bool {
        if self.is_on_curve() {
            self.x.exp_biguint(&FIELD_NUM_SQUARES) != ECField::ONE
        } else {
            false
        }
    }
}

impl From<HomogPoint> for Point {
    fn from(value: HomogPoint) -> Self {
        Self {
            x: value.x / value.z,
            u: value.u / value.t,
        }
    }
}

impl Add<Self> for Point {
    type Output = Self;

    fn add(self, rhs: Point) -> Self::Output {
        self.add_homog(rhs).into()
    }
}

impl AddAssign<Self> for Point {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul<Point> for &BigUint {
    type Output = Point;
    fn mul(self, rhs: Point) -> Self::Output {
        (0..self.bits()).rev().fold(Point::ZERO, |prod, bit_pos| {
            let double = prod.double();
            if self.bit(bit_pos) {
                double + rhs
            } else {
                double
            }
        })
    }
}

type FieldTarget = OEFTarget<5, QuinticExtension<GoldilocksField>>;

#[derive(Clone, Debug)]
pub struct PointTarget {
    pub x: FieldTarget,
    pub u: FieldTarget,
}

impl PointTarget {
    pub fn to_value(&self, builder: &mut CircuitBuilder<GoldilocksField, 2>) -> ValueTarget {
        let hash = builder.hash_n_to_m_no_pad::<PoseidonHash>(
            self.x
                .components
                .iter()
                .chain(self.u.components.iter())
                .cloned()
                .collect(),
            4,
        );
        ValueTarget::from_slice(&hash)
    }
}

#[derive(Clone, Debug)]
struct PointSquareRootGenerator {
    pub orig: PointTarget,
    pub sqrt: PointTarget,
}

impl<const D: usize> SimpleGenerator<GoldilocksField, D> for PointSquareRootGenerator
where
    GoldilocksField: Extendable<D>,
{
    fn id(&self) -> String {
        "PointSquareRootGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<plonky2::iop::target::Target> {
        let mut deps = Vec::with_capacity(10);
        deps.extend_from_slice(&self.orig.x.components);
        deps.extend_from_slice(&self.orig.u.components);
        deps
    }

    fn run_once(
        &self,
        witness: &plonky2::iop::witness::PartitionWitness<GoldilocksField>,
        out_buffer: &mut plonky2::iop::generator::GeneratedValues<GoldilocksField>,
    ) -> anyhow::Result<()> {
        let pt = Point {
            x: get_nnf_target(witness, &self.orig.x),
            u: get_nnf_target(witness, &self.orig.u),
        };
        let sqrt = &*GROUP_ORDER_HALF_ROUND_UP * pt;
        out_buffer.set_target_arr(&self.sqrt.x.components, &sqrt.x.0)?;
        out_buffer.set_target_arr(&self.sqrt.u.components, &sqrt.u.0)
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<GoldilocksField, D>,
    ) -> plonky2::util::serialization::IoResult<()> {
        dst.write_target_array(&self.orig.x.components)?;
        dst.write_target_array(&self.orig.u.components)?;
        dst.write_target_array(&self.sqrt.x.components)?;
        dst.write_target_array(&self.sqrt.u.components)
    }

    fn deserialize(
        src: &mut plonky2::util::serialization::Buffer,
        _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<GoldilocksField, D>,
    ) -> plonky2::util::serialization::IoResult<Self>
    where
        Self: Sized,
    {
        let orig = PointTarget {
            x: FieldTarget::new(src.read_target_array()?),
            u: FieldTarget::new(src.read_target_array()?),
        };
        let sqrt = PointTarget {
            x: FieldTarget::new(src.read_target_array()?),
            u: FieldTarget::new(src.read_target_array()?),
        };
        Ok(Self { orig, sqrt })
    }
}

pub trait CircuitBuilderElliptic {
    fn add_virtual_point_target(&mut self) -> PointTarget;
    fn identity_point(&mut self) -> PointTarget;
    fn constant_point(&mut self, p: Point) -> PointTarget;

    fn add_point(&mut self, p1: &PointTarget, p2: &PointTarget) -> PointTarget;
    fn double_point(&mut self, p: &PointTarget) -> PointTarget;
    fn linear_combination_points(
        &mut self,
        p1_scalar: &[BoolTarget; 320],
        p2_scalar: &[BoolTarget; 320],
        p1: &PointTarget,
        p2: &PointTarget,
    ) -> PointTarget;
    fn if_point(
        &mut self,
        b: BoolTarget,
        p_true: &PointTarget,
        p_false: &PointTarget,
    ) -> PointTarget;

    /// Check that two points are equal.  This assumes that the points are
    /// already known to be in the subgroup.
    fn connect_point(&mut self, p1: &PointTarget, p2: &PointTarget);
    fn check_point_on_curve(&mut self, p: &PointTarget);
    fn check_point_in_subgroup(&mut self, p: &PointTarget);
}

impl CircuitBuilderElliptic for CircuitBuilder<GoldilocksField, 2> {
    fn add_virtual_point_target(&mut self) -> PointTarget {
        let p = PointTarget {
            x: self.add_virtual_nnf_target(),
            u: self.add_virtual_nnf_target(),
        };
        self.check_point_in_subgroup(&p);
        p
    }

    fn identity_point(&mut self) -> PointTarget {
        self.constant_point(Point::ZERO)
    }

    fn constant_point(&mut self, p: Point) -> PointTarget {
        assert!(p.is_in_subgroup());
        PointTarget {
            x: self.nnf_constant(&p.x),
            u: self.nnf_constant(&p.u),
        }
    }

    fn add_point(&mut self, p1: &PointTarget, p2: &PointTarget) -> PointTarget {
        let mut inputs = Vec::with_capacity(20);
        inputs.extend_from_slice(&p1.x.components);
        inputs.extend_from_slice(&p1.u.components);
        inputs.extend_from_slice(&p2.x.components);
        inputs.extend_from_slice(&p2.u.components);
        let mut outputs = ECAddHomog::apply(self, &inputs);
        // plonky2 expects all gate constraints to be satisfied by the zero vector.
        // So our elliptic curve addition gate computes [x,z-b,u,t-b], and we have to add the b here.
        let b1 = self.constant(Point::B1);
        outputs[6] = self.add(outputs[6], b1);
        outputs[16] = self.add(outputs[16], b1);
        let x = FieldTarget::new(outputs[0..5].try_into().unwrap());
        let z = FieldTarget::new(outputs[5..10].try_into().unwrap());
        let u = FieldTarget::new(outputs[10..15].try_into().unwrap());
        let t = FieldTarget::new(outputs[15..20].try_into().unwrap());
        let xq = self.nnf_div(&x, &z);
        let uq = self.nnf_div(&u, &t);
        PointTarget { x: xq, u: uq }
        /*
        let t1 = self.nnf_mul(&p1.x, &p2.x);
        let t3 = self.nnf_mul(&p1.u, &p2.u);
        let t5 = self.nnf_add(&p1.x, &p2.x);
        let t6 = self.nnf_add(&p1.u, &p2.u);
        let b1 = self.constant(GoldilocksField::from_canonical_u32(Point::B1_U32));
        let t7 = self.nnf_add_scalar_times_generator_power(b1, 1, &t1);
        let t9_1 = self.nnf_mul_generator(&t5);
        let t9_2 = self.nnf_mul_scalar(b1, &t9_1);
        let t9_3 = self.nnf_add(&t9_2, &t7);
        let t9_4 = self.nnf_add(&t9_3, &t9_3);
        let t9 = self.nnf_mul(&t3, &t9_4);
        let one = self.one();
        let t10_1 = self.nnf_add(&t3, &t3);
        let t10_2 = self.nnf_add_scalar_times_generator_power(one, 0, &t10_1);
        let t10_3 = self.nnf_add(&t5, &t7);
        let t10 = self.nnf_mul(&t10_2, &t10_3);
        let x_1 = self.nnf_sub(&t10, &t7);
        let x_2 = self.nnf_mul_generator(&x_1);
        let x = self.nnf_mul_scalar(b1, &x_2);
        let z = self.nnf_sub(&t7, &t9);
        let neg_one = self.neg_one();
        let u_1 = self.nnf_mul_scalar(neg_one, &t1);
        let u_2 = self.nnf_add_scalar_times_generator_power(b1, 1, &u_1);
        let u = self.nnf_mul(&t6, &u_2);
        let t = self.nnf_add(&t7, &t9);
        let xq = self.nnf_div(&x, &z);
        let uq = self.nnf_div(&u, &t);
        PointTarget { x: xq, u: uq }
        */
    }

    fn double_point(&mut self, p: &PointTarget) -> PointTarget {
        self.add_point(p, p)
        /*
        let t3 = self.nnf_mul(&p.u, &p.u);
        let one = self.one();
        let neg_one = self.neg_one();
        let two = self.two();
        let neg_four = self.constant(GoldilocksField::from_noncanonical_i64(-4));
        let four_b = self.constant(GoldilocksField::from_canonical_u32(4 * Point::B1_U32));
        let w1_1 = self.nnf_add_scalar_times_generator_power(one, 0, &p.x);
        let w1_2 = self.nnf_add(&w1_1, &w1_1);
        let w1_3 = self.nnf_mul(&w1_2, &t3);
        let w1_4 = self.nnf_mul_scalar(neg_one, &w1_3);
        let w1 = self.nnf_add_scalar_times_generator_power(one, 0, &w1_4);
        let x_1 = self.nnf_mul_scalar(four_b, &t3);
        let x = self.nnf_mul_generator(&x_1);
        let z = self.nnf_mul(&w1, &w1);
        let u_1 = self.nnf_add(&w1, &p.u);
        let u_2 = self.nnf_mul(&u_1, &u_1);
        let u_3 = self.nnf_sub(&u_2, &t3);
        let u = self.nnf_sub(&u_3, &z);
        let t_1 = self.nnf_mul_scalar(neg_four, &t3);
        let t_2 = self.nnf_add_scalar_times_generator_power(two, 0, &t_1);
        let t = self.nnf_sub(&t_2, &z);
        let xq = self.nnf_div(&x, &z);
        let uq = self.nnf_div(&u, &t);
        PointTarget { x: xq, u: uq }
        */
    }

    fn linear_combination_points(
        &mut self,
        p1_scalar: &[BoolTarget; 320],
        p2_scalar: &[BoolTarget; 320],
        p1: &PointTarget,
        p2: &PointTarget,
    ) -> PointTarget {
        let zero = self.identity_point();
        let sum = self.add_point(p1, p2);
        let mut ans = zero.clone();
        for i in (0..320).rev() {
            ans = self.double_point(&ans);
            let maybe_p1 = self.if_point(p1_scalar[i], p1, &zero);
            let p2_maybe_p1 = self.if_point(p1_scalar[i], &sum, p2);
            let p = self.if_point(p2_scalar[i], &p2_maybe_p1, &maybe_p1);
            ans = self.add_point(&ans, &p);
        }
        ans
    }

    fn if_point(
        &mut self,
        b: BoolTarget,
        p_true: &PointTarget,
        p_false: &PointTarget,
    ) -> PointTarget {
        PointTarget {
            x: self.nnf_if(b, &p_true.x, &p_false.x),
            u: self.nnf_if(b, &p_true.u, &p_false.u),
        }
    }

    fn connect_point(&mut self, p1: &PointTarget, p2: &PointTarget) {
        // The elements of the subgroup have distinct u-coordinates.  So it
        // is not necessary to connect the x-coordinates.
        // Explanation: If a point has u-coordinate lambda:
        // If lambda is nonzero, then the other two points on the line x = lambda y
        // are the origin (which has u=0 rather than lambda) and a point that's not
        // in our subgroup (it differs from an element of our subgroup by
        // a 2-torsion point).
        // If lambda is zero, then the line x = 0 is tangent to the origin and also
        // passes through the point at infinity (which is not in our subgroup).
        self.nnf_connect(&p1.u, &p2.u);
    }

    fn check_point_on_curve(&mut self, p: &PointTarget) {
        let t1 = self.nnf_mul(&p.u, &p.u);
        let two = self.two();
        let t2 = self.nnf_add_scalar_times_generator_power(two, 0, &p.x);
        let t3 = self.nnf_mul(&p.x, &t2);
        let b1 = self.constant(Point::B1);
        let t4 = self.nnf_add_scalar_times_generator_power(b1, 1, &t3);
        let t5 = self.nnf_mul(&t1, &t4);
        self.nnf_connect(&p.x, &t5);
    }

    fn check_point_in_subgroup(&mut self, p: &PointTarget) {
        // In order to be in the subgroup, the point needs to be a multiple
        // of two.
        let sqrt = PointTarget {
            x: self.add_virtual_nnf_target(),
            u: self.add_virtual_nnf_target(),
        };
        self.check_point_on_curve(&sqrt);
        let doubled = self.double_point(&sqrt);
        // connect_point assumes that the point is already known to be in the
        // subgroup, so connect the coordinates instead
        self.nnf_connect(&doubled.x, &p.x);
        self.nnf_connect(&doubled.u, &p.u);
        self.add_simple_generator(PointSquareRootGenerator {
            orig: p.clone(),
            sqrt,
        });
    }
}

pub trait WitnessWriteCurve: WitnessWrite<GoldilocksField> {
    fn set_field_target(&mut self, target: &FieldTarget, value: &ECField) -> anyhow::Result<()> {
        self.set_target_arr(&target.components, &value.0)
    }
    fn set_point_target(&mut self, target: &PointTarget, value: &Point) -> anyhow::Result<()> {
        self.set_field_target(&target.x, &value.x)?;
        self.set_field_target(&target.u, &value.u)
    }
    fn set_biguint320_target(
        &mut self,
        target: &BigUInt320Target,
        value: &BigUint,
    ) -> anyhow::Result<()> {
        assert!(value.bits() <= 320);
        let digits = value.to_u32_digits();
        for i in 0..10 {
            let d = digits.get(i).copied().unwrap_or(0);
            self.set_target(target.0[i], GoldilocksField::from_canonical_u32(d))?;
        }
        Ok(())
    }
}

impl<W: WitnessWrite<GoldilocksField>> WitnessWriteCurve for W {}

#[cfg(test)]
mod test {
    use num::{BigUint, FromPrimitive};
    use num_bigint::RandBigInt;
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::rngs::OsRng;

    use crate::backends::plonky2::primitives::ec::{
        bits::CircuitBuilderBits,
        curve::{CircuitBuilderElliptic, ECField, Point, WitnessWriteCurve, GROUP_ORDER},
    };

    #[test]
    fn test_double() {
        let g = Point::generator();
        let p1 = g + g;
        let p2 = g.double();
        assert_eq!(p1, p2);
    }

    #[test]
    fn test_id() {
        let p1 = Point::generator();
        let p2 = p1 + Point::ZERO;
        assert_eq!(p1, p2);
    }

    #[test]
    fn test_triple() {
        let g = Point::generator();
        let p1 = g + g + g;
        let p2 = g + g.double();
        let three = BigUint::from_u64(3).unwrap();
        let p3 = (&three) * g;
        assert_eq!(p1, p2);
        assert_eq!(p2, p3);
    }

    #[test]
    fn test_associativity() {
        let g = Point::generator();
        let n1 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let n2 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let prod = (&n1 * &n2) % &*GROUP_ORDER;
        assert_eq!(&prod * g, &n1 * (&n2 * g));
    }

    #[test]
    fn test_distributivity() {
        let g = Point::generator();
        let n1 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let n2 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let sum = (&n1 + &n2) % &*GROUP_ORDER;
        let p1 = &n1 * g;
        let p2 = &n2 * g;
        let psum = &sum * g;
        assert_eq!(p1 + p2, psum);
    }

    #[test]
    fn test_in_subgroup() {
        let g = Point::generator();
        assert!(g.is_in_subgroup());
        let n = OsRng.gen_biguint_below(&GROUP_ORDER);
        assert!((&n * g).is_in_subgroup());
        let fake = Point {
            x: ECField::ONE,
            u: ECField::ONE,
        };
        assert!(!fake.is_on_curve());
        let not_sub = Point {
            x: Point::b() / g.x,
            u: g.u,
        };
        assert!(not_sub.is_on_curve());
        assert!(!not_sub.is_in_subgroup());
    }

    #[test]
    fn test_double_circuit() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let g = Point::generator();
        let n = OsRng.gen_biguint_below(&GROUP_ORDER);
        let p = (&n) * g;
        let a = builder.constant_point(p);
        let b = builder.double_point(&a);
        let c = builder.constant_point(p.double());
        builder.connect_point(&b, &c);
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_add_circuit() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let g = Point::generator();
        let n1 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let n2 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let p1 = (&n1) * g;
        let p2 = (&n2) * g;
        let a = builder.constant_point(p1);
        let b = builder.constant_point(p2);
        let c = builder.add_point(&a, &b);
        let d = builder.constant_point(p1 + p2);
        builder.connect_point(&c, &d);
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_linear_combination_circuit() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let g = Point::generator();
        let n1 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let n2 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let n3 = OsRng.gen_biguint_below(&GROUP_ORDER);
        let p = (&n1) * g;
        let g_tgt = builder.constant_point(g);
        let p_tgt = builder.constant_point(p);
        let g_scalar_bigint = builder.constant_biguint320(&n2);
        let p_scalar_bigint = builder.constant_biguint320(&n3);
        let g_scalar_bits = builder.biguint_bits(&g_scalar_bigint);
        let p_scalar_bits = builder.biguint_bits(&p_scalar_bigint);
        let e = builder.constant_point((&n2) * g + (&n3) * p);
        let f = builder.linear_combination_points(&g_scalar_bits, &p_scalar_bits, &g_tgt, &p_tgt);
        builder.connect_point(&e, &f);
        let pw = PartialWitness::new();
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let proof = data.prove(pw)?;
        data.verify(proof)?;
        Ok(())
    }

    #[test]
    fn test_not_in_subgroup_circuit() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let g = Point::generator();
        let not_sub = Point {
            x: Point::b() / g.x,
            u: g.u,
        };
        let pt = builder.add_virtual_point_target();
        let mut pw = PartialWitness::new();
        pw.set_point_target(&pt, &not_sub)?;
        let data = builder.build::<PoseidonGoldilocksConfig>();
        assert!(data.prove(pw).is_err());
        Ok(())
    }
}
