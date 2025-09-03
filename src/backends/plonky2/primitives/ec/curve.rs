//! Implementation of the elliptic curve ecGFp5.
//!
//! We roughly follow pornin/ecgfp5.
use core::ops::{Add, Mul};
use std::{
    array, fmt,
    ops::{AddAssign, Neg, Sub},
    str::FromStr,
    sync::LazyLock,
};

use num::{bigint::BigUint, Num, One};
use num_bigint::RandBigInt;
use plonky2::{
    field::{
        extension::{quintic::QuinticExtension, Extendable, FieldExtension, Frobenius},
        goldilocks_field::GoldilocksField,
        ops::Square,
        types::{Field, Field64, PrimeField},
    },
    hash::poseidon::PoseidonHash,
    iop::{generator::SimpleGenerator, target::BoolTarget, witness::WitnessWrite},
    plonk::circuit_builder::CircuitBuilder,
    util::serialization::{Read, Write},
};
use rand::rngs::OsRng;
use schemars::JsonSchema;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::backends::plonky2::{
    circuits::common::ValueTarget,
    primitives::ec::{
        bits::BigUInt320Target,
        field::{get_nnf_target, CircuitBuilderNNF, OEFTarget},
        gates::curve::{ECAddHomogOffsetGate, ECAddXuGate},
    },
    Error,
};

type ECField = QuinticExtension<GoldilocksField>;

/// Computes sqrt in ECField as sqrt(x) = sqrt(x^r)/x^((r-1)/2) with r
/// = 1 + p + ... + p^4, where the numerator involves a sqrt in
/// GoldilocksField, cf.
/// https://github.com/pornin/ecgfp5/blob/ce059c6d1e1662db437aecbf3db6bb67fe63c716/rust/src/field.rs#L1041
pub fn ec_field_sqrt(x: &ECField) -> Option<ECField> {
    // Compute x^r.
    let x_to_the_r = (0..5)
        .map(|i| x.repeated_frobenius(i))
        .reduce(|a, b| a * b)
        .expect("Iterator should be nonempty.");
    let num = QuinticExtension([
        x_to_the_r.0[0].sqrt()?,
        GoldilocksField::ZERO,
        GoldilocksField::ZERO,
        GoldilocksField::ZERO,
        GoldilocksField::ZERO,
    ]);
    // Compute x^((r-1)/2) = x^(p*((1+p)/2)*(1+p^2))
    let x1 = x.frobenius();
    #[allow(clippy::manual_div_ceil)]
    let x2 = x1.exp_u64((1 + GoldilocksField::ORDER) / 2);
    let den = x2 * x2.repeated_frobenius(2);
    Some(num / den)
}

fn ec_field_to_bytes(x: &ECField) -> Vec<u8> {
    x.0.iter()
        .flat_map(|f| {
            f.to_canonical_biguint()
                .to_bytes_le()
                .into_iter()
                .chain(std::iter::repeat(0u8))
                .take(8)
        })
        .collect()
}

fn ec_field_from_bytes(b: &[u8]) -> Result<ECField, Error> {
    let fields: Vec<_> = b
        .chunks(8)
        .map(|chunk| {
            GoldilocksField::from_canonical_u64(
                BigUint::from_bytes_le(chunk)
                    .try_into()
                    .expect("Slice should not contain more than 8 bytes."),
            )
        })
        .collect();

    if fields.len() != 5 {
        return Err(Error::custom(
            "Invalid byte encoding of quintic extension field element.".to_string(),
        ));
    }

    Ok(QuinticExtension(array::from_fn(|i| fields[i])))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point {
    pub x: ECField,
    pub u: ECField,
}

impl JsonSchema for Point {
    fn schema_name() -> String {
        "Point".to_string()
    }

    fn json_schema(gen: &mut schemars::gen::SchemaGenerator) -> schemars::schema::Schema {
        <String>::json_schema(gen)
    }
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[allow(clippy::collapsible_else_if)]
        if f.alternate() {
            write!(f, "({}, {})", self.x, self.u)
        } else {
            if self.is_in_subgroup() {
                // Compressed
                let u_bytes = self.as_bytes_from_subgroup().expect("point in subgroup");
                let u_b58 = bs58::encode(u_bytes).into_string();
                write!(f, "{}", u_b58)
            } else {
                // Non-compressed
                let xu_bytes = [ec_field_to_bytes(&self.x), ec_field_to_bytes(&self.u)].concat();
                let xu_b58 = bs58::encode(xu_bytes).into_string();
                write!(f, "{}", xu_b58)
            }
        }
    }
}

impl FromStr for Point {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let point_bytes = bs58::decode(s)
            .into_vec()
            .map_err(|e| Error::custom(format!("Base58 decode error: {}", e)))?;

        if point_bytes.len() == 80 {
            // Non-compressed
            Ok(Point {
                x: ec_field_from_bytes(&point_bytes[..40])?,
                u: ec_field_from_bytes(&point_bytes[40..])?,
            })
        } else {
            // Compressed
            Self::from_bytes_into_subgroup(&point_bytes)
        }
    }
}

impl Serialize for Point {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let point_b58 = format!("{}", self);
        serializer.serialize_str(&point_b58)
    }
}

impl<'de> Deserialize<'de> for Point {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let point_b58 = String::deserialize(deserializer)?;
        Self::from_str(&point_b58).map_err(serde::de::Error::custom)
    }
}

impl Point {
    pub fn new_rand_from_subgroup() -> Self {
        &OsRng.gen_biguint_below(&GROUP_ORDER) * Self::generator()
    }
    pub fn as_fields(&self) -> Vec<crate::middleware::F> {
        self.x.0.iter().chain(self.u.0.iter()).cloned().collect()
    }
    pub fn compress_from_subgroup(&self) -> Result<ECField, Error> {
        match self.is_in_subgroup() {
            true => Ok(self.u),
            false => Err(Error::custom(format!(
                "Point must lie in EC subgroup: {}",
                self
            ))),
        }
    }
    pub fn decompress_into_subgroup(u: &ECField) -> Result<Self, Error> {
        if u == &ECField::ZERO {
            return Ok(Self::ZERO);
        }
        // Figure out x.
        let b = ECField::TWO - ECField::ONE / (u.square());
        let d = b.square() - ECField::TWO.square() * Self::b();
        let alpha = ECField::NEG_ONE * b / ECField::TWO;
        let beta = ec_field_sqrt(&d)
            .ok_or(Error::custom(format!("Not a quadratic residue: {}", d)))?
            / ECField::TWO;
        let mut points = [ECField::ONE, ECField::NEG_ONE].into_iter().map(|s| Point {
            x: alpha + s * beta,
            u: *u,
        });
        points.find(|p| p.is_in_subgroup()).ok_or(Error::custom(
            "One of the points must lie in the EC subgroup.".into(),
        ))
    }
    pub fn as_bytes_from_subgroup(&self) -> Result<Vec<u8>, Error> {
        self.compress_from_subgroup().map(|u| ec_field_to_bytes(&u))
    }
    pub fn from_bytes_into_subgroup(b: &[u8]) -> Result<Self, Error> {
        ec_field_from_bytes(b).and_then(|u| Self::decompress_into_subgroup(&u))
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

    /// Multiplies a point (viewed as an extension field element) by a
    /// small factor times the field extension generator.
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

    /// Adds a factor times the extension field generator to a point
    /// (viewed as an extension field element).
    fn add_field_gen(self, factor: GoldilocksField) -> Self {
        let mut b1 = self.to_base();
        let mut b2 = b1[1].to_basefield_array();
        b2[0] += factor;
        b1[1] = Self::Base::from_basefield_array(b2);
        Self::from_base(b1)
    }

    /// Adds a scalar (base field element) to a point (viewed as an
    /// extension field element).
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

/// Adds two elliptic curve points in affine coordinates.
pub(super) fn add_xu<const D: usize, F: ECFieldExt<D> + std::ops::Div<Output = F>>(
    x1: F,
    u1: F,
    x2: F,
    u2: F,
) -> [F; 2] {
    let [x, z, u, t] = add_homog(x1, u1, x2, u2);
    [x / z, u / t]
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
pub static GROUP_ORDER: LazyLock<BigUint> = LazyLock::new(|| {
    BigUint::from_str_radix(GROUP_ORDER_STR, 10)
        .expect("The input should be a valid decimal string.")
});

static FIELD_NUM_SQUARES: LazyLock<BigUint> =
    LazyLock::new(|| (ECField::order() - BigUint::one()) >> 1);

static GROUP_ORDER_HALF_ROUND_UP: LazyLock<BigUint> =
    LazyLock::new(|| (&*GROUP_ORDER + BigUint::one()) >> 1);

impl Point {
    const B1_U32: u32 = 263;
    pub(crate) const B1: GoldilocksField = GoldilocksField(Self::B1_U32 as u64);

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
        let bits = self.to_radix_be(2);
        bits.into_iter().fold(Point::ZERO, |prod, bit| {
            let double = prod.double();
            if bit == 1 {
                double + rhs
            } else {
                double
            }
        })
    }
}

type FieldTarget = OEFTarget<5, QuinticExtension<GoldilocksField>>;

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct PointTarget {
    pub x: FieldTarget,
    pub u: FieldTarget,
    pub(super) checked_on_curve: bool,
    pub(super) checked_in_subgroup: bool,
}

impl PointTarget {
    pub fn new_unsafe(x: FieldTarget, u: FieldTarget) -> Self {
        Self {
            x,
            u,
            checked_on_curve: false,
            checked_in_subgroup: false,
        }
    }
    pub fn to_value(&self, builder: &mut CircuitBuilder<GoldilocksField, 2>) -> ValueTarget {
        let hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(
            self.x
                .components
                .iter()
                .chain(self.u.components.iter())
                .cloned()
                .collect(),
        );
        ValueTarget::from_slice(&hash.elements)
    }
}

#[derive(Clone, Default, Debug)]
pub(crate) struct PointSquareRootGenerator {
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
        dst.write_bool(self.orig.checked_on_curve)?;
        dst.write_bool(self.orig.checked_in_subgroup)?;
        dst.write_target_array(&self.sqrt.x.components)?;
        dst.write_target_array(&self.sqrt.u.components)?;
        dst.write_bool(self.sqrt.checked_on_curve)?;
        dst.write_bool(self.sqrt.checked_in_subgroup)
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
            checked_on_curve: src.read_bool()?,
            checked_in_subgroup: src.read_bool()?,
        };
        let sqrt = PointTarget {
            x: FieldTarget::new(src.read_target_array()?),
            u: FieldTarget::new(src.read_target_array()?),
            checked_on_curve: src.read_bool()?,
            checked_in_subgroup: src.read_bool()?,
        };
        Ok(Self { orig, sqrt })
    }
}

pub trait CircuitBuilderSignature {
    /// Computes `a*g + b*p`, where `g` is the generator of the curve.
    fn linear_combination_point_gen(
        &mut self,
        a: &[BoolTarget; 320],
        b: &[BoolTarget; 320],
        p: &PointTarget,
    ) -> PointTarget;
}

impl CircuitBuilderSignature for CircuitBuilder<GoldilocksField, 2> {
    fn linear_combination_point_gen(
        &mut self,
        a: &[BoolTarget; 320],
        b: &[BoolTarget; 320],
        p: &PointTarget,
    ) -> PointTarget {
        let y = p;
        let zero = self.identity_point();
        let zero_target = self.zero();

        let mut ans = zero.clone(); // accumulator

        for x in 0..107 {
            // prepare to apply gate
            let mut inputs = Vec::with_capacity(26);

            // scalar bits for g
            if x == 0 {
                inputs.push(zero_target);
            } else {
                inputs.push(a[320 - 3 * x].target);
            }
            inputs.push(a[319 - 3 * x].target);
            inputs.push(a[318 - 3 * x].target);

            // scalar bits for p (y)
            if x == 0 {
                inputs.push(zero_target);
            } else {
                inputs.push(b[320 - 3 * x].target);
            }
            inputs.push(b[319 - 3 * x].target);
            inputs.push(b[318 - 3 * x].target);

            // y point
            inputs.extend_from_slice(&y.x.components);
            inputs.extend_from_slice(&y.u.components);

            // accumulator
            inputs.extend_from_slice(&ans.x.components);
            inputs.extend_from_slice(&ans.u.components);

            // apply gate
            let outputs = ECAddXuGate::apply(self, &inputs);
            let x = FieldTarget::new(array::from_fn(|i| outputs[i]));
            let u = FieldTarget::new(array::from_fn(|i| outputs[5 + i]));
            ans = PointTarget {
                x,
                u,
                checked_on_curve: true,
                checked_in_subgroup: p.checked_in_subgroup,
            };
        }

        ans
    }
}

pub trait CircuitBuilderElliptic {
    fn add_virtual_point_target_unsafe(&mut self) -> PointTarget;
    fn add_virtual_point_target(&mut self) -> PointTarget;
    fn identity_point(&mut self) -> PointTarget;
    fn constant_point(&mut self, p: Point) -> PointTarget;

    fn add_point(&mut self, p1: &PointTarget, p2: &PointTarget) -> PointTarget;
    fn double_point(&mut self, p: &PointTarget) -> PointTarget;
    fn multiply_point(&mut self, p1_scalar: &[BoolTarget; 320], p1: &PointTarget) -> PointTarget;
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
    fn check_point_on_curve(&mut self, p: &mut PointTarget);
    fn check_point_in_subgroup(&mut self, p: &mut PointTarget);
}

impl CircuitBuilderElliptic for CircuitBuilder<GoldilocksField, 2> {
    fn add_virtual_point_target_unsafe(&mut self) -> PointTarget {
        PointTarget::new_unsafe(self.add_virtual_nnf_target(), self.add_virtual_nnf_target())
    }
    fn add_virtual_point_target(&mut self) -> PointTarget {
        let mut p = self.add_virtual_point_target_unsafe();
        self.check_point_in_subgroup(&mut p);
        p
    }

    fn identity_point(&mut self) -> PointTarget {
        self.constant_point(Point::ZERO)
    }

    fn constant_point(&mut self, p: Point) -> PointTarget {
        assert!(p.is_in_subgroup(), "Given point should be in EC subgroup.");
        let mut p_target =
            PointTarget::new_unsafe(self.nnf_constant(&p.x), self.nnf_constant(&p.u));
        self.check_point_in_subgroup(&mut p_target);
        p_target
    }

    fn add_point(&mut self, p1: &PointTarget, p2: &PointTarget) -> PointTarget {
        assert!(
            p1.checked_on_curve && p2.checked_on_curve,
            "EC addition formula requires that both points lie on the curve."
        );
        let mut inputs = Vec::with_capacity(20);
        inputs.extend_from_slice(&p1.x.components);
        inputs.extend_from_slice(&p1.u.components);
        inputs.extend_from_slice(&p2.x.components);
        inputs.extend_from_slice(&p2.u.components);

        let outputs = ECAddHomogOffsetGate::apply(self, &inputs);

        // plonky2 expects all gate constraints to be satisfied by the zero vector.
        // So our elliptic curve addition gate computes [x,z-b,u,t-b], and we have to add the b here.
        let [x, z, u, t] =
            array::from_fn(|j| FieldTarget::new(array::from_fn(|i| outputs[5 * j + i])));
        let b1 = self.constant(Point::B1);
        let z = self.nnf_add_scalar_times_generator_power(b1, 1, &z);
        let t = self.nnf_add_scalar_times_generator_power(b1, 1, &t);
        let xq = self.nnf_div(&x, &z);
        let uq = self.nnf_div(&u, &t);
        // If p1 and p2 lie in the subgroup, then so does p1 + p2.
        PointTarget {
            x: xq,
            u: uq,
            checked_on_curve: true,
            checked_in_subgroup: p1.checked_in_subgroup && p2.checked_in_subgroup,
        }
    }

    fn double_point(&mut self, p: &PointTarget) -> PointTarget {
        self.add_point(p, p)
    }

    fn multiply_point(&mut self, p1_scalar: &[BoolTarget; 320], p1: &PointTarget) -> PointTarget {
        let zero = self.identity_point();
        let mut ans = zero.clone();
        for i in (0..320).rev() {
            ans = self.double_point(&ans);
            let maybe_p1 = self.if_point(p1_scalar[i], p1, &zero);
            ans = self.add_point(&ans, &maybe_p1);
        }
        ans
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
            checked_on_curve: p_true.checked_on_curve && p_false.checked_on_curve,
            checked_in_subgroup: p_true.checked_in_subgroup && p_false.checked_in_subgroup,
        }
    }

    fn connect_point(&mut self, p1: &PointTarget, p2: &PointTarget) {
        assert!(
            p1.checked_in_subgroup && p2.checked_in_subgroup,
            "Connected points must lie in the EC subgroup."
        );
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

    fn check_point_on_curve(&mut self, p: &mut PointTarget) {
        let t1 = self.nnf_mul(&p.u, &p.u);
        let two = self.two();
        let t2 = self.nnf_add_scalar_times_generator_power(two, 0, &p.x);
        let t3 = self.nnf_mul(&p.x, &t2);
        let b1 = self.constant(Point::B1);
        let t4 = self.nnf_add_scalar_times_generator_power(b1, 1, &t3);
        let t5 = self.nnf_mul(&t1, &t4);
        self.nnf_connect(&p.x, &t5);
        p.checked_on_curve = true;
    }

    fn check_point_in_subgroup(&mut self, p: &mut PointTarget) {
        // In order to be in the subgroup, the point needs to be a multiple
        // of two.
        let mut sqrt = self.add_virtual_point_target_unsafe();
        self.check_point_on_curve(&mut sqrt);
        let doubled = self.double_point(&sqrt);
        // connect_point assumes that the point is already known to be in the
        // subgroup, so connect the coordinates instead
        self.nnf_connect(&doubled.x, &p.x);
        self.nnf_connect(&doubled.u, &p.u);
        self.add_simple_generator(PointSquareRootGenerator {
            orig: p.clone(),
            sqrt,
        });
        p.checked_on_curve = true;
        p.checked_in_subgroup = true;
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
            self.set_target(target.limbs[i], GoldilocksField::from_canonical_u32(d))?;
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
        field::{
            extension::quintic::QuinticExtension,
            goldilocks_field::GoldilocksField,
            ops::Square,
            types::{Field, Sample},
        },
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::rngs::OsRng;

    use crate::backends::plonky2::{
        primitives::ec::{
            bits::CircuitBuilderBits,
            curve::{
                ec_field_sqrt, CircuitBuilderElliptic, ECField, Point, WitnessWriteCurve,
                GROUP_ORDER,
            },
        },
        Error,
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
    fn test_sqrt() {
        let x = QuinticExtension::rand().square();
        let y = ec_field_sqrt(&x);
        assert_eq!(y.map(|a| a.square()), Some(x));
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
    fn test_roundtrip_compression() -> Result<(), Error> {
        (0..10).try_for_each(|_| {
            let p = Point::new_rand_from_subgroup();
            let p_compressed = p.compress_from_subgroup()?;
            let q = Point::decompress_into_subgroup(&p_compressed)?;

            match p == q {
                true => Ok(()),
                false => Err(Error::custom(format!(
                    "Roundtrip compression failed: {} ≠ {}",
                    p, q
                ))),
            }
        })
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
        let g_scalar_bits = g_scalar_bigint.bits;
        let p_scalar_bits = p_scalar_bigint.bits;
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

    #[test]
    fn test_point_serialize_deserialize() -> Result<(), anyhow::Error> {
        // In subgroup
        let g = Point::generator();

        let serialized = serde_json::to_string_pretty(&g)?;
        println!("g = {}", serialized);
        let deserialized = serde_json::from_str(&serialized)?;
        assert_eq!(g, deserialized);

        // Not in subgroup
        let not_sub = Point {
            x: Point::b() / g.x,
            u: g.u,
        };

        let serialized = serde_json::to_string_pretty(&not_sub)?;
        println!("not_sub = {}", serialized);
        let deserialized = serde_json::from_str(&serialized)?;
        assert_eq!(not_sub, deserialized);

        Ok(())
    }
}
