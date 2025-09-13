use std::{array, ops::Range};

use itertools::{zip_eq, Itertools};
use plonky2::{
    field::{
        extension::{quintic::QuinticExtension, Extendable, FieldExtension, OEF},
        goldilocks_field::GoldilocksField,
        types::Field,
    },
    gates::gate::Gate,
    hash::hash_types::RichField,
    iop::{
        ext_target::ExtensionTarget,
        generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef},
        target::Target,
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData},
        vars::{EvaluationTargets, EvaluationVars},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};

use crate::backends::plonky2::{
    basetypes::F,
    primitives::ec::{
        curve::{add_homog, add_homog_offset, add_xu, ECFieldExt, Point},
        gates::field::{nnf_mul_ext, QuinticTensor},
    },
};

/// Gate computing the addition of two elliptic curve points in
/// homogeneous coordinates *minus* an offset in the `z` and `t`
/// coordinates, viz. the extension field generator times `Point::B1`,
/// cf. CircuitBuilderElliptic::add_point.
///
/// In plonky2 one Gate can do multiple operations and the gate will register one
/// generator per operation.  When a gate operation is used, the `CircuitBuilder` tracks the
/// allocation of operations to gates via the `current_slots` field.  Once the circuit is fully
/// defined, during the build the circuit the generators
/// associated to unused operations (free slots) are removed:
/// <https://github.com/0xPolygonZero/plonky2/blob/82791c4809d6275682c34b926390ecdbdc2a5297/plonky2/src/plonk/circuit_builder.rs#L1210>
/// Since the generator for the unused operations are removed, no witness value will be calculated
/// for them, and the free slots gate witness wires will be filled with the default value which is zero:
/// <https://github.com/0xPolygonZero/plonky2/blob/82791c4809d6275682c34b926390ecdbdc2a5297/plonky2/src/iop/witness.rs#L377>
/// This means that a gate with multiple operations need to pass the constraints for a single
/// operation when all its witness wire values are zero (so that when the gate is partially used,
/// the unused slots still pass the constraints). This is the reason why this gate doesn't add the
/// final offset: if it did, the constraints wouldn't pass on the zero witness values.
#[derive(Debug, Clone)]
pub struct ECAddHomogOffsetGate {
    /// Number of (offset) EC additions performed by the gate.
    pub num_ops: usize,
}

impl ECAddHomogOffsetGate {
    pub const fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
        }
    }

    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 40;
        config.num_routed_wires / wires_per_op
    }

    pub(crate) const fn wires_ith_addend_0(i: usize) -> Range<usize> {
        40 * i..40 * i + 10
    }
    pub(crate) const fn wires_ith_addend_1(i: usize) -> Range<usize> {
        40 * i + 10..40 * i + 20
    }
    pub(crate) const fn wires_ith_output(i: usize) -> Range<usize> {
        40 * i + 20..40 * (i + 1)
    }

    pub fn apply<const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        targets: &[Target],
    ) -> Vec<Target>
    where
        F: Extendable<D>,
    {
        let gate = ECAddHomogOffsetGate::new_from_config(&builder.config);
        let (row, op_num) = builder.find_slot(gate, &[], &[]);
        let wires_a0 = Self::wires_ith_addend_0(op_num)
            .map(|i| Target::wire(row, i))
            .collect::<Vec<_>>();
        let wires_a1 = Self::wires_ith_addend_1(op_num)
            .map(|i| Target::wire(row, i))
            .collect::<Vec<_>>();
        let outputs = Self::wires_ith_output(op_num)
            .map(|i| Target::wire(row, i))
            .collect::<Vec<_>>();
        zip_eq(targets, [wires_a0, wires_a1].concat()).for_each(|(i, w)| builder.connect(*i, w));

        outputs
    }
}

impl<const D: usize> Gate<F, D> for ECAddHomogOffsetGate
where
    F: Extendable<D>,
{
    fn id(&self) -> String {
        format!("{self:?}")
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let num_ops = src.read_usize()?;
        Ok(Self { num_ops })
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<<F as Extendable<D>>::Extension> {
        let mut constraints = Vec::with_capacity(self.num_ops * 20);
        let extract_point = |range: Range<usize>| -> (QuinticTensor<D>, QuinticTensor<D>) {
            let components = vars.local_wires[range].to_vec();
            (
                QuinticTensor::from_base(array::from_fn::<_, 5, _>(|i| components[i])),
                QuinticTensor::from_base(array::from_fn::<_, 5, _>(|i| components[i + 5])),
            )
        };

        for i in 0..self.num_ops {
            let (a_0x, a_0u) = extract_point(Self::wires_ith_addend_0(i));
            let (a_1x, a_1u) = extract_point(Self::wires_ith_addend_1(i));
            let output_vec = vars.local_wires[Self::wires_ith_output(i)]
                .iter()
                .chunks(5)
                .into_iter()
                .map(|chunk| {
                    let chunk_vec = chunk.collect::<Vec<_>>();
                    QuinticTensor::from_base(array::from_fn(|i| *chunk_vec[i]))
                })
                .collect::<Vec<QuinticTensor<D>>>();
            let computed_output = add_homog_offset(a_0x, a_0u, a_1x, a_1u);

            let new_constraints =
                zip_eq(output_vec, computed_output).flat_map(|(o, co)| (o - co).components);

            constraints.extend(new_constraints);
        }

        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(self.num_ops * 20);

        let extract_point =
            |range: Range<usize>| -> ([ExtensionTarget<D>; 5], [ExtensionTarget<D>; 5]) {
                let components = vars.local_wires[range].to_vec();
                (
                    array::from_fn::<_, 5, _>(|i| components[i]),
                    array::from_fn::<_, 5, _>(|i| components[i + 5]),
                )
            };
        for i in 0..self.num_ops {
            let (x1, u1) = extract_point(Self::wires_ith_addend_0(i));
            let (x2, u2) = extract_point(Self::wires_ith_addend_1(i));
            let computed_output = ec_target_add_homog_offset(builder, &x1, &u1, &x2, &u2)
                .into_iter()
                .flatten();

            let output: [ExtensionTarget<D>; 20] = vars.local_wires[Self::wires_ith_output(i)]
                .try_into()
                .unwrap();

            let diffs = zip_eq(output, computed_output)
                .map(|(o, co)| builder.sub_extension(o, co))
                .collect::<Vec<_>>();
            constraints.extend(diffs);
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops)
            .map(|i| WitnessGeneratorRef::new(ECAddHomogOffsetGenerator { row, i }.adapter()))
            .collect()
    }

    fn num_wires(&self) -> usize {
        self.num_ops * 40
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        4
    }

    fn num_constraints(&self) -> usize {
        self.num_ops * 20
    }
}

#[derive(Clone, Debug, Default)]
pub struct ECAddHomogOffsetGenerator {
    row: usize,
    i: usize,
}

impl<const D: usize> SimpleGenerator<F, D> for ECAddHomogOffsetGenerator
where
    F: Extendable<D>,
{
    fn id(&self) -> String {
        "ECAddHomogOffsetGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        ECAddHomogOffsetGate::wires_ith_addend_0(self.i)
            .chain(ECAddHomogOffsetGate::wires_ith_addend_1(self.i))
            .map(|i| Target::wire(self.row, i))
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> anyhow::Result<()> {
        let extract_point = |range: Range<usize>| -> anyhow::Result<_> {
            let components = range
                .map(|i| witness.get_target(Target::wire(self.row, i)))
                .collect::<Vec<_>>();
            Ok((
                QuinticExtension::from_basefield_array(array::from_fn::<_, 5, _>(|i| {
                    components[i]
                })),
                QuinticExtension::from_basefield_array(array::from_fn::<_, 5, _>(|i| {
                    components[i + 5]
                })),
            ))
        };

        let addend_0 = extract_point(ECAddHomogOffsetGate::wires_ith_addend_0(self.i))?;
        let addend_1 = extract_point(ECAddHomogOffsetGate::wires_ith_addend_1(self.i))?;

        let output_targets: [Target; 20] = ECAddHomogOffsetGate::wires_ith_output(self.i)
            .map(|i| Target::wire(self.row, i))
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|e| anyhow::anyhow!("{:?}", e))?;

        let computed_output = add_homog_offset(addend_0.0, addend_0.1, addend_1.0, addend_1.1)
            .iter()
            .flat_map(<QuinticExtension<F> as FieldExtension<5>>::to_basefield_array)
            .collect::<Vec<_>>();

        out_buffer.set_target_arr(&output_targets, &computed_output)
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        Ok(Self { row, i })
    }
}

#[derive(Clone, Debug, Default)]
pub struct ECAddXuGenerator {
    row: usize,
}

impl<const D: usize> SimpleGenerator<F, D> for ECAddXuGenerator
where
    F: Extendable<D>,
{
    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(
        src: &mut Buffer,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            row: src.read_usize()?,
        })
    }

    fn id(&self) -> String {
        "ECAddXuGenerator".into()
    }

    fn dependencies(&self) -> Vec<Target> {
        (0..26).map(|i| Target::wire(self.row, i)).collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<GoldilocksField>,
        out_buffer: &mut GeneratedValues<GoldilocksField>,
    ) -> anyhow::Result<()> {
        let deps = self.dependencies();

        let selectors_g: Vec<GoldilocksField> = deps[0..3]
            .iter() // binary selectors for g
            .map(|&target| witness.get_target(target))
            .collect();

        let selectors_y: Vec<GoldilocksField> = deps[3..6]
            .iter() // binary selectors for y
            .map(|&target| witness.get_target(target))
            .collect();

        // extract element of quintic extension of Goldilocks field from five consecutive targets
        let extract_quintic = |start_idx: usize| -> QuinticExtension<GoldilocksField> {
            QuinticExtension::<GoldilocksField>::from_basefield_array([
                witness.get_target(deps[start_idx]),
                witness.get_target(deps[start_idx + 1]),
                witness.get_target(deps[start_idx + 2]),
                witness.get_target(deps[start_idx + 3]),
                witness.get_target(deps[start_idx + 4]),
            ])
        };

        let g = Point::generator();

        let g_x = g.x;
        let g_u = g.u;
        let y_x = extract_quintic(6);
        let y_u = extract_quintic(11);

        let mut p_x = extract_quintic(16);
        let mut p_u = extract_quintic(21);

        let mut write_quintic =
            |start_wire: usize, value: &QuinticExtension<GoldilocksField>| -> anyhow::Result<()> {
                let array: [GoldilocksField; 5] =
                    QuinticExtension::<GoldilocksField>::to_basefield_array(value);
                for (j, &num) in array.iter().enumerate() {
                    out_buffer.set_target(Target::wire(self.row, start_wire + j), num)?;
                }
                Ok(())
            };

        // Double and add three times.
        // Write points from right to left so that the result of the fifth add
        // lies on a routable wire and thus can be copied to the next row.
        (0..3).try_for_each(|i| {
            // Double, write to wires [106-30*i..116-30*i]
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, p_x, p_u);
            write_quintic(106 - 30 * i, &p_x)?;
            write_quintic(111 - 30 * i, &p_u)?;

            // Possibly add g, depending on selector. Write to wires  [96-30*i..106-30*i]
            if selectors_g[i] == GoldilocksField::ONE {
                [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, g_x, g_u);
            }
            write_quintic(96 - 30 * i, &p_x)?;
            write_quintic(101 - 30 * i, &p_u)?;

            // Possibly add y, depending on selector. Write to wires  [86-30*i..96-30*i]
            if selectors_y[i] == GoldilocksField::ONE {
                [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, y_x, y_u);
            }
            write_quintic(86 - 30 * i, &p_x)?;
            write_quintic(91 - 30 * i, &p_u)
        })
    }
}

/// Gate that selectively carries out three rounds of the
/// double-and-add algorithm loop applied to the curve generator and a
/// given point.
#[derive(Clone)]
pub struct ECAddXuGate;

impl ECAddXuGate {
    const INPUTS_PER_OP: usize = 26;
    const OUTPUTS_PER_OP: usize = 90;
    const WIRES_PER_OP: usize = Self::INPUTS_PER_OP + Self::OUTPUTS_PER_OP;
    const DEGREE: usize = 6;
    const ID: &'static str = "ECAddXuGate";

    pub fn apply<const D: usize>(
        builder: &mut CircuitBuilder<F, D>,
        targets: &[Target],
    ) -> Vec<Target>
    where
        F: Extendable<D>,
    {
        assert!(targets.len() == Self::INPUTS_PER_OP);
        let (row, _) = builder.find_slot(ECAddXuGate::new(), &[], &[]);
        for (i, &t) in targets.iter().enumerate() {
            builder.connect(t, Target::wire(row, i));
        }

        (0..10)
            .map(|i| Target::wire(row, Self::INPUTS_PER_OP + i))
            .collect()
    }

    pub fn new() -> Self {
        Self
    }

    pub fn add_numerator_denominator<const D: usize>(
        wires: &[<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension],
    ) -> Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension>
    where
        GoldilocksField: plonky2::field::extension::Extendable<D>,
    {
        let mut ans = Vec::with_capacity(20);
        let x1 = QuinticTensor::from_base(wires[0..5].try_into().unwrap());
        let u1 = QuinticTensor::from_base(wires[5..10].try_into().unwrap());
        let x2 = QuinticTensor::from_base(wires[10..15].try_into().unwrap());
        let u2 = QuinticTensor::from_base(wires[15..20].try_into().unwrap());
        let out = add_homog(x1, u1, x2, u2);
        for v in out {
            ans.extend(v.to_base());
        }
        ans
    }

    pub fn convert<const D: usize>(
        wires: &[<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension],
    ) -> Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension>
    where
        GoldilocksField: plonky2::field::extension::Extendable<D>,
    {
        let mut ans = Vec::with_capacity(10);
        let x1 = QuinticTensor::from_base(wires[0..5].try_into().unwrap());
        let u1 = QuinticTensor::from_base(wires[5..10].try_into().unwrap());
        ans.extend(x1.to_base());
        ans.extend(u1.to_base());
        ans
    }
}

impl<const D: usize> Gate<F, D> for ECAddXuGate
where
    F: Extendable<D>,
{
    fn id(&self) -> String {
        Self::ID.to_string()
    }

    fn serialize(
        &self,
        _dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(
        _src: &mut Buffer<'_>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self)
    }

    fn eval_unfiltered(
        &self,
        vars: EvaluationVars<'_, GoldilocksField, D>,
    ) -> Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension> {
        let mut constraints = Vec::new();

        let g = Point::generator();

        let double_constraint = |i: usize, j: usize| {
            let x1 = QuinticTensor::from_base(vars.local_wires[i..i + 5].try_into().unwrap());
            let u1 = QuinticTensor::from_base(vars.local_wires[i + 5..i + 10].try_into().unwrap());
            let [x, z, u, t] = add_homog(x1, u1, x1, u1);
            let mut new_constraints: Vec<
                <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension,
            > = Vec::with_capacity(10);
            let x2 = QuinticTensor::from_base(vars.local_wires[j..j + 5].try_into().unwrap());
            let u2 = QuinticTensor::from_base(vars.local_wires[j + 5..j + 10].try_into().unwrap());

            let first_constraints: Vec<_> = (x2 * z - x).components.to_vec();
            let second_constraints: Vec<_> = (u2 * t - u).components.to_vec();

            new_constraints.extend(&first_constraints);
            new_constraints.extend(&second_constraints);
            new_constraints
        };

        let select_and_add_constraint = |i: usize, j: usize, selector_index: usize, add_y: bool| {
            let zero =
                <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension::ZERO;

            let one = <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension::ONE;
            let one_full = QuinticTensor::from_base([one, zero, zero, zero, zero]);

            let sel = vars.local_wires[selector_index];
            let sel_full = QuinticTensor::from_base([sel, zero, zero, zero, zero]);

            let x1 = QuinticTensor::from_base(vars.local_wires[i..i + 5].try_into().unwrap());
            let u1 = QuinticTensor::from_base(vars.local_wires[i + 5..i + 10].try_into().unwrap());

            let (x2, u2);
            if add_y {
                // (using hardcoded location of y)
                x2 = QuinticTensor::from_base(vars.local_wires[6..11].try_into().unwrap());
                u2 = QuinticTensor::from_base(vars.local_wires[11..16].try_into().unwrap());
            } else {
                let mut base_array: [GoldilocksField; 5] = g.x.to_basefield_array();
                x2 = QuinticTensor::from_base(base_array.map(Into::into));
                base_array = g.u.to_basefield_array();
                u2 = QuinticTensor::from_base(base_array.map(Into::into));
            }
            let [x, z, u, t] = add_homog(x1, u1, x2, u2);

            let mut new_constraints: Vec<
                <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension,
            > = Vec::with_capacity(10);
            let x3 = QuinticTensor::from_base(vars.local_wires[j..j + 5].try_into().unwrap());
            let u3 = QuinticTensor::from_base(vars.local_wires[j + 5..j + 10].try_into().unwrap());

            let first_constraints: Vec<_> = (x3 * z - sel_full * x
                + (sel_full - one_full) * x1 * z)
                .components
                .to_vec();
            let second_constraints: Vec<_> = (u3 * t - sel_full * u
                + (sel_full - one_full) * u1 * t)
                .components
                .to_vec();

            new_constraints.extend_from_slice(&first_constraints[0..5]);
            new_constraints.extend_from_slice(&second_constraints[0..5]);
            new_constraints
        };

        constraints.extend(double_constraint(16, 106));
        constraints.extend(select_and_add_constraint(106, 96, 0, false));
        constraints.extend(select_and_add_constraint(96, 86, 3, true));

        constraints.extend(double_constraint(86, 76));
        constraints.extend(select_and_add_constraint(76, 66, 1, false));
        constraints.extend(select_and_add_constraint(66, 56, 4, true));

        constraints.extend(double_constraint(56, 46));
        constraints.extend(select_and_add_constraint(46, 36, 2, false));
        constraints.extend(select_and_add_constraint(36, 26, 5, true));

        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<GoldilocksField, D>,
        vars: EvaluationTargets<'_, D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::new();

        type Nnf = QuinticExtension<F>;

        let zero = builder.zero_extension();

        let g = Point::generator();
        let [g_x, g_u]: [[F; 5]; 2] = [g.x.to_basefield_array(), g.u.to_basefield_array()];
        let [g_x_ext_target, g_u_ext_target] = [
            array::from_fn(|i| builder.add_const_extension(zero, g_x[i])),
            array::from_fn(|i| builder.add_const_extension(zero, g_u[i])),
        ];

        let double_constraint =
            |builder: &mut CircuitBuilder<GoldilocksField, D>, i: usize, j: usize| {
                let x1 = array::from_fn(|k| vars.local_wires[i + k]);
                let u1 = array::from_fn(|k| vars.local_wires[i + 5 + k]);
                let [x, z, u, t] = homog_ec_target_add(builder, &x1, &u1, &x1, &u1);

                let mut new_constraints = Vec::<ExtensionTarget<_>>::with_capacity(10);
                let x2 = array::from_fn(|k| vars.local_wires[j + k]);
                let u2 = array::from_fn(|k| vars.local_wires[j + 5 + k]);

                let [expected_x, expected_u] = [
                    nnf_mul_ext::<D, 5, Nnf>(builder, &x2, &z),
                    nnf_mul_ext::<D, 5, Nnf>(builder, &u2, &t),
                ];
                let first_constraints = nnf_ext_target_sub::<D, 5, Nnf>(builder, &expected_x, &x);
                let second_constraints = nnf_ext_target_sub::<D, 5, Nnf>(builder, &expected_u, &u);

                new_constraints.extend(&first_constraints);
                new_constraints.extend(&second_constraints);
                new_constraints
            };

        let select_and_add_constraint = |builder: &mut CircuitBuilder<GoldilocksField, D>,
                                         i: usize,
                                         j: usize,
                                         selector_index: usize,
                                         add_y: bool| {
            let one = builder.one_extension();
            let sel = vars.local_wires[selector_index];

            let x1 = array::from_fn(|k| vars.local_wires[i + k]);
            let u1 = array::from_fn(|k| vars.local_wires[i + 5 + k]);

            let (x2, u2) = if add_y {
                // (using hardcoded location of y)
                (
                    array::from_fn(|k| vars.local_wires[6 + k]),
                    array::from_fn(|k| vars.local_wires[11 + k]),
                )
            } else {
                (g_x_ext_target, g_u_ext_target)
            };

            let [x, z, u, t] = homog_ec_target_add(builder, &x1, &u1, &x2, &u2);

            let mut new_constraints = Vec::<ExtensionTarget<_>>::with_capacity(10);
            let x3 = array::from_fn(|k| vars.local_wires[j + k]);
            let u3 = array::from_fn(|k| vars.local_wires[j + 5 + k]);

            let sel_minus_one = builder.sub_extension(sel, one);
            let first_constraints = {
                let term1 = nnf_mul_ext::<D, 5, Nnf>(builder, &x3, &z);
                let term2 = array::from_fn(|i| builder.mul_extension(sel, x[i]));
                let term3_1 = array::from_fn(|i| builder.mul_extension(sel_minus_one, x1[i]));
                let term3 = nnf_mul_ext::<D, 5, Nnf>(builder, &term3_1, &z);
                let partial_sum = nnf_ext_target_sub::<D, 5, Nnf>(builder, &term1, &term2);
                nnf_ext_target_add::<D, 5, Nnf>(builder, &partial_sum, &term3)
            };

            let second_constraints = {
                let term1 = nnf_mul_ext::<D, 5, Nnf>(builder, &u3, &t);
                let term2 = array::from_fn(|i| builder.mul_extension(sel, u[i]));
                let term3_1 = array::from_fn(|i| builder.mul_extension(sel_minus_one, u1[i]));
                let term3 = nnf_mul_ext::<D, 5, Nnf>(builder, &term3_1, &t);
                let partial_sum = nnf_ext_target_sub::<D, 5, Nnf>(builder, &term1, &term2);
                nnf_ext_target_add::<D, 5, Nnf>(builder, &partial_sum, &term3)
            };

            new_constraints.extend(first_constraints);
            new_constraints.extend(second_constraints);
            new_constraints
        };

        constraints.extend(double_constraint(builder, 16, 106));
        constraints.extend(select_and_add_constraint(builder, 106, 96, 0, false));
        constraints.extend(select_and_add_constraint(builder, 96, 86, 3, true));

        constraints.extend(double_constraint(builder, 86, 76));
        constraints.extend(select_and_add_constraint(builder, 76, 66, 1, false));
        constraints.extend(select_and_add_constraint(builder, 66, 56, 4, true));

        constraints.extend(double_constraint(builder, 56, 46));
        constraints.extend(select_and_add_constraint(builder, 46, 36, 2, false));
        constraints.extend(select_and_add_constraint(builder, 36, 26, 5, true));

        constraints
    }

    fn generators(
        &self,
        row: usize,
        _local_constants: &[GoldilocksField],
    ) -> Vec<WitnessGeneratorRef<GoldilocksField, D>> {
        vec![WitnessGeneratorRef::new(ECAddXuGenerator { row }.adapter())]
    }

    fn num_wires(&self) -> usize {
        Self::WIRES_PER_OP
    }

    fn degree(&self) -> usize {
        Self::DEGREE
    }

    fn num_ops(&self) -> usize {
        1
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn num_constraints(&self) -> usize {
        90
    }
}

// Useful auxiliary methods for defining the above gate follow.
fn nnf_ext_target_add<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    y: &[ExtensionTarget<D>; DEG],
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    let sum_target = zip_eq(x, y)
        .map(|(a, b)| builder.add_extension(*a, *b))
        .collect::<Vec<_>>();
    array::from_fn(|i| sum_target[i])
}

fn nnf_ext_target_sub<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    y: &[ExtensionTarget<D>; DEG],
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    let diff_target = zip_eq(x, y)
        .map(|(a, b)| builder.sub_extension(*a, *b))
        .collect::<Vec<_>>();
    array::from_fn(|i| diff_target[i])
}

fn nnf_ext_target_add_field_gen<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    factor: NNF::BaseField,
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    array::from_fn(|i| {
        if i == 1 {
            builder.add_const_extension(x[1], factor)
        } else {
            x[i]
        }
    })
}

fn nnf_ext_target_mul_field_gen<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    factor: NNF::BaseField,
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    array::from_fn(|i| {
        if i == 0 {
            builder.mul_const_extension(factor * NNF::W, x[DEG - 1])
        } else {
            builder.mul_const_extension(factor, x[i - 1])
        }
    })
}

fn nnf_ext_target_add_scalar<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    scal: NNF::BaseField,
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    array::from_fn(|i| {
        if i == 0 {
            builder.add_const_extension(x[0], scal)
        } else {
            x[i]
        }
    })
}

fn homog_ec_target_addition_terms<const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x1: &[ExtensionTarget<D>; 5],
    u1: &[ExtensionTarget<D>; 5],
    x2: &[ExtensionTarget<D>; 5],
    u2: &[ExtensionTarget<D>; 5],
) -> [[ExtensionTarget<D>; 5]; 5]
where
    F: Extendable<D>,
{
    type Nnf = QuinticExtension<F>;

    let t1 = nnf_mul_ext::<D, 5, Nnf>(builder, x1, x2);
    let t3 = nnf_mul_ext::<D, 5, Nnf>(builder, u1, u2);
    let t5 = nnf_ext_target_add::<D, 5, Nnf>(builder, x1, x2);
    let t6 = nnf_ext_target_add::<D, 5, Nnf>(builder, u1, u2);
    let t7 = nnf_ext_target_add_field_gen::<D, 5, Nnf>(builder, &t1, Point::B1);

    let twice_t7 = nnf_ext_target_add::<D, 5, Nnf>(builder, &t7, &t7);
    let t5_mul_fg2b =
        nnf_ext_target_mul_field_gen::<D, 5, Nnf>(builder, &t5, Point::B1 + Point::B1);
    let t5_mul_fg2b_plus_twice_t7 =
        nnf_ext_target_add::<D, 5, Nnf>(builder, &t5_mul_fg2b, &twice_t7);
    let t9 = nnf_mul_ext::<D, 5, Nnf>(builder, &t3, &t5_mul_fg2b_plus_twice_t7);

    let t5_plus_t7 = nnf_ext_target_add::<D, 5, Nnf>(builder, &t5, &t7);
    let twice_t3 = nnf_ext_target_add::<D, 5, Nnf>(builder, &t3, &t3);
    let twice_t3_plus_one =
        nnf_ext_target_add_scalar::<D, 5, Nnf>(builder, &twice_t3, GoldilocksField::ONE);
    let t10 = nnf_mul_ext::<D, 5, Nnf>(builder, &twice_t3_plus_one, &t5_plus_t7);
    [t1, t6, t7, t9, t10]
}

// TODO: Make this more generic?
/// Analogue of `add_homog` for extension targets.
fn homog_ec_target_add<const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x1: &[ExtensionTarget<D>; 5],
    u1: &[ExtensionTarget<D>; 5],
    x2: &[ExtensionTarget<D>; 5],
    u2: &[ExtensionTarget<D>; 5],
) -> [[ExtensionTarget<D>; 5]; 4]
where
    F: Extendable<D>,
{
    type Nnf = QuinticExtension<F>;

    let [t1, t6, t7, t9, t10] = homog_ec_target_addition_terms(builder, x1, u1, x2, u2);

    let t10_minus_t7 = nnf_ext_target_sub::<D, 5, Nnf>(builder, &t10, &t7);
    let x = nnf_ext_target_mul_field_gen::<D, 5, Nnf>(builder, &t10_minus_t7, Point::B1);

    let z = nnf_ext_target_sub::<D, 5, Nnf>(builder, &t7, &t9);

    let minus_t1 = array::from_fn(|i| builder.mul_const_extension(-F::ONE, t1[i]));
    let minus_t1_plus_fgpb =
        nnf_ext_target_add_field_gen::<D, 5, Nnf>(builder, &minus_t1, Point::B1);
    let u = nnf_mul_ext::<D, 5, Nnf>(builder, &t6, &minus_t1_plus_fgpb);

    let t = nnf_ext_target_add::<D, 5, Nnf>(builder, &t7, &t9);

    [x, z, u, t]
}

/// Analogue of `add_homog_offset` for extension targets.
fn ec_target_add_homog_offset<const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x1: &[ExtensionTarget<D>; 5],
    u1: &[ExtensionTarget<D>; 5],
    x2: &[ExtensionTarget<D>; 5],
    u2: &[ExtensionTarget<D>; 5],
) -> [[ExtensionTarget<D>; 5]; 4]
where
    F: Extendable<D>,
{
    type Nnf = QuinticExtension<F>;

    let [t1, t6, t7, t9, t10] = homog_ec_target_addition_terms(builder, x1, u1, x2, u2);

    let t10_minus_t7 = nnf_ext_target_sub::<D, 5, Nnf>(builder, &t10, &t7);
    let x = nnf_ext_target_mul_field_gen::<D, 5, Nnf>(builder, &t10_minus_t7, Point::B1);

    let z = nnf_ext_target_sub::<D, 5, Nnf>(builder, &t1, &t9);

    let minus_t1 = array::from_fn(|i| builder.mul_const_extension(-F::ONE, t1[i]));
    let minus_t1_plus_fgpb =
        nnf_ext_target_add_field_gen::<D, 5, Nnf>(builder, &minus_t1, Point::B1);
    let u = nnf_mul_ext::<D, 5, Nnf>(builder, &t6, &minus_t1_plus_fgpb);

    let t = nnf_ext_target_add::<D, 5, Nnf>(builder, &t1, &t9);

    [x, z, u, t]
}

#[cfg(test)]
mod test {
    use plonky2::{
        gates::gate_testing::{test_eval_fns, test_low_degree},
        plonk::{circuit_data::CircuitConfig, config::PoseidonGoldilocksConfig},
    };

    use crate::backends::plonky2::primitives::ec::gates::curve::{
        ECAddHomogOffsetGate, ECAddXuGate,
    };

    #[test]
    fn test_ec_add_gate() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = ECAddHomogOffsetGate::new_from_config(&config);

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(gate)
    }

    #[test]
    fn test_ec_add_xu_gate() -> Result<(), anyhow::Error> {
        let gate = ECAddXuGate::new();

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(gate)
    }

    #[test]
    fn test_ec_add_gate_low_degree() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = ECAddHomogOffsetGate::new_from_config(&config);

        test_low_degree::<_, _, 2>(gate);
        Ok(())
    }

    #[test]
    fn test_ec_add_xu_gate_low_degree() -> Result<(), anyhow::Error> {
        let gate = ECAddXuGate::new();

        test_low_degree::<_, _, 2>(gate);
        Ok(())
    }
}
