use std::marker::PhantomData;
use plonky2::{
    gates::gate::Gate,
    field::goldilocks_field::GoldilocksField,
    field::extension::quintic::QuinticExtension,
    field::{
        types::Field,
        extension::{FieldExtension, Extendable},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CommonCircuitData,
        vars::{EvaluationTargets, EvaluationVars},
    },
    iop::{
        generator::{WitnessGeneratorRef, SimpleGenerator, GeneratedValues},
        target::Target,
        witness::{PartitionWitness, WitnessWrite, Witness},
        ext_target::ExtensionTarget,
    },
    util::serialization::{IoResult, Buffer, Write, Read},
};
use crate::backends::plonky2::primitives::ec::{
    curve::{add_homog_offset, ECFieldExt, add_homog, add_xu, Point},
    gates::{field::QuinticTensor, generic::SimpleGate},
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
/// https://github.com/0xPolygonZero/plonky2/blob/82791c4809d6275682c34b926390ecdbdc2a5297/plonky2/src/plonk/circuit_builder.rs#L1210
/// Since the generator for the unused operations are removed, no witness value will be calculated
/// for them, and the free slots gate witness wires will be filled with the default value which is zero:
/// https://github.com/0xPolygonZero/plonky2/blob/82791c4809d6275682c34b926390ecdbdc2a5297/plonky2/src/iop/witness.rs#L377
/// This means that a gate with multiple operations need to pass the constraints for a single
/// operation when all its witness wire values are zero (so that when the gate is partially used,
/// the unused slots still pass the constraints). This is the reason why this gate doesn't add the
/// final offset: if it did, the constraints wouldn't pass on the zero witness values.
#[derive(Debug, Clone)]
pub struct ECAddHomogOffset;

impl SimpleGate for ECAddHomogOffset {
    type F = GoldilocksField;
    const INPUTS_PER_OP: usize = 20;
    const OUTPUTS_PER_OP: usize = 20;
    const DEGREE: usize = 4;
    const ID: &'static str = "ECAddHomog";
    fn eval<const D: usize>(
        wires: &[<Self::F as plonky2::field::extension::Extendable<D>>::Extension],
    ) -> Vec<<Self::F as plonky2::field::extension::Extendable<D>>::Extension>
    where
        Self::F: plonky2::field::extension::Extendable<D>,
    {
        let mut ans = Vec::with_capacity(20);
        let x1 = QuinticTensor::from_base(wires[0..5].try_into().unwrap());
        let u1 = QuinticTensor::from_base(wires[5..10].try_into().unwrap());
        let x2 = QuinticTensor::from_base(wires[10..15].try_into().unwrap());
        let u2 = QuinticTensor::from_base(wires[15..20].try_into().unwrap());
        let out = add_homog_offset(x1, u1, x2, u2);
        for v in out {
            ans.extend(v.to_base());
        }
        ans
    }
}

#[derive(Debug)]
pub struct ECAddXuGenerator {
    row: usize,
}

impl<const D: usize> SimpleGenerator<GoldilocksField, D> for ECAddXuGenerator
where
    GoldilocksField: plonky2::field::extension::Extendable<D>,
{
    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<GoldilocksField, D>) -> IoResult<Self>
    where
        Self: Sized,
    {
        Ok(Self {
            row: src.read_usize()?
        })
    }

    fn id(&self) -> String {
        format!("Generator<{},{}>", D, "ECAddXuGenerator")
    }

    fn dependencies(&self) -> Vec<Target> {
        (0..30).map(|i| Target::wire(self.row, i))
        .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<GoldilocksField>,
        out_buffer: &mut GeneratedValues<GoldilocksField>,
    ) -> anyhow::Result<()> {

        let deps = self.dependencies();

        let selectors_g: Vec<GoldilocksField> = deps[0..3].iter() // binary selectors for g
            .map(|&target| witness.get_target(target))
            .collect();
        
        let selectors_y: Vec<GoldilocksField> = deps[5..8].iter() // binary selectors for y
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
        let y_x = extract_quintic(10);
        let y_u = extract_quintic(15);

        let mut p_x = extract_quintic(20);
        let mut p_u = extract_quintic(25);

        let mut write_quintic = |start_wire: usize, value: &QuinticExtension<GoldilocksField>| -> anyhow::Result<()> {
            let array: [GoldilocksField; 5] = QuinticExtension::<GoldilocksField>::to_basefield_array(value);
            for (j, &num) in array.iter().enumerate() {
                out_buffer.set_target(Target::wire(self.row, start_wire + j), num)?;
            }
            Ok(())
        };

        // Double and add three times.
        // Write points from right to left so that the result of the fifth add
        // lies on a routable wire and thus can be copied to the next row.

        // Double, write to wires [125..135]
        [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, p_x, p_u);
        write_quintic(125, &p_x)?;
        write_quintic(130, &p_u)?;

        // Possibly add g, depending on selector. Write to wires  [115..125]
        if selectors_g[0] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, g_x, g_u);
        }
        write_quintic(115, &p_x)?;
        write_quintic(120, &p_u)?;

        // Possibly add y, depending on selector. Write to wires  [105..115]
        if selectors_y[0] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, y_x, y_u);
        }
        write_quintic(105, &p_x)?;
        write_quintic(110, &p_u)?;

        // Repeat, total of three times.
        [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, p_x, p_u);
        write_quintic(95, &p_x)?;
        write_quintic(100, &p_u)?;
        if selectors_g[1] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, g_x, g_u);
        }
        write_quintic(85, &p_x)?;
        write_quintic(90, &p_u)?;
        if selectors_y[1] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, y_x, y_u);
        }
        write_quintic(75, &p_x)?;
        write_quintic(80, &p_u)?;
        
        [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, p_x, p_u);
        write_quintic(65, &p_x)?;
        write_quintic(70, &p_u)?;
        if selectors_g[2] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, g_x, g_u);
        }
        write_quintic(55, &p_x)?;
        write_quintic(60, &p_u)?;
        if selectors_y[2] == GoldilocksField::ONE {
            [p_x, p_u] = add_xu::<1, QuinticExtension<GoldilocksField>>(p_x, p_u, y_x, y_u);
        }
        write_quintic(45, &p_x)?;
        write_quintic(50, &p_u)?;

        
        Ok(())
    }
}

#[derive(Clone)]
pub struct ECAddXu {
    pub max_ops: usize,
    pub recursive_max_wires: usize,
    pub _gate: PhantomData<()>,
}

impl ECAddXu {
    const INPUTS_PER_OP: usize = 30;
    const OUTPUTS_PER_OP: usize = 105;
    const WIRES_PER_OP: usize = Self::INPUTS_PER_OP + Self::OUTPUTS_PER_OP;
    const DEGREE: usize = 5;
    const ID: &'static str = "ECAddXu";

    
    pub fn apply<const D: usize>(
        builder: &mut CircuitBuilder<GoldilocksField, D>,
        targets: &[Target],
        row: usize,
    ) -> Vec<Target>
    where
        GoldilocksField: Extendable<D>,
    {
        assert!(targets.len() == Self::INPUTS_PER_OP);
        for (i, &t) in targets.iter().enumerate() {
            builder.connect(t, Target::wire(row, i));
        }
        (0..105)
            .map(|i| Target::wire(row, 30 + i))
            .collect()
    }
    

    pub fn new_from_config() -> Self {
        Self {
            max_ops: 1,
            recursive_max_wires: 80,
            _gate: PhantomData,
        }
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

impl<const D: usize> Gate<GoldilocksField, D> for ECAddXu
where
    GoldilocksField: plonky2::field::extension::Extendable<D>,
{
    fn id(&self) -> String {
        Self::ID.to_string()
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.max_ops)
    }

    fn deserialize(
        src: &mut Buffer<'_>,
        _common_data: &CommonCircuitData<GoldilocksField, D>,
    ) -> IoResult<Self>
    where
        Self: Sized,
    {
        let max_ops = src.read_usize()?;
        Ok(Self {
            max_ops,
            recursive_max_wires: 80,
            _gate: PhantomData,
        })
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<'_, GoldilocksField, D>) -> Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension> {
        let mut constraints = Vec::new();

        let g = Point::generator();

        let double_constraint = |i: usize, j: usize| {

            let x1 = QuinticTensor::from_base(vars.local_wires[i..i+5].try_into().unwrap());
            let u1 = QuinticTensor::from_base(vars.local_wires[i+5..i+10].try_into().unwrap());
            let x2 = QuinticTensor::from_base(vars.local_wires[i..i+5].try_into().unwrap());
            let u2 = QuinticTensor::from_base(vars.local_wires[i+5..i+10].try_into().unwrap());
            let [x, z, u, t] = add_homog(x1, u1, x2, u2);
            let mut new_constraints: Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension> = Vec::with_capacity(10);
            let x3 = QuinticTensor::from_base(vars.local_wires[j..j+5].try_into().unwrap());
            let u3 = QuinticTensor::from_base(vars.local_wires[j+5..j+10].try_into().unwrap());

            let first_constraints: Vec<_> = (x3 * z - x).components.to_vec();
            let second_constraints: Vec<_> = (u3 * t - u).components.to_vec();
            
            
            new_constraints.extend(&first_constraints);
            new_constraints.extend(&second_constraints);
            new_constraints
        };

        let select_and_add_constraint = |i: usize, j: usize, selector_index: usize, add_y: bool| {
            let zero = <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension::ZERO;

            let one = <GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension::ONE;
            let one_full = QuinticTensor::from_base([one, zero, zero, zero, zero]);

            let sel = vars.local_wires[selector_index];
            let sel_full = QuinticTensor::from_base([sel, zero, zero, zero, zero]);

            let x1 = QuinticTensor::from_base(vars.local_wires[i..i+5].try_into().unwrap());
            let u1 = QuinticTensor::from_base(vars.local_wires[i+5..i+10].try_into().unwrap());

            let (x2, u2);
            if add_y {
                // (using hardcoded location of y)
                x2 = QuinticTensor::from_base(vars.local_wires[10..15].try_into().unwrap());
                u2 = QuinticTensor::from_base(vars.local_wires[15..20].try_into().unwrap());
            } else {
                let mut base_array: [GoldilocksField; 5] = g.x.to_basefield_array();
                x2 = QuinticTensor::from_base(base_array.map(Into::into).try_into().unwrap());
                base_array = g.u.to_basefield_array();
                u2 = QuinticTensor::from_base(base_array.map(Into::into).try_into().unwrap());
            }
            let [x, z, u, t] = add_homog(x1, u1, x2, u2);

            let mut new_constraints: Vec<<GoldilocksField as plonky2::field::extension::Extendable<D>>::Extension> = Vec::with_capacity(10);
            let x3 = QuinticTensor::from_base(vars.local_wires[j..j+5].try_into().unwrap());
            let u3 = QuinticTensor::from_base(vars.local_wires[j+5..j+10].try_into().unwrap());

            let first_constraints: Vec<_> = (x3 * z - sel_full * x + (sel_full - one_full) * x1 * z).components.to_vec();
            let second_constraints: Vec<_> = (u3 * t - sel_full * u + (sel_full - one_full) * u1 * t).components.to_vec();
            
            new_constraints.extend_from_slice(&first_constraints[0..5]);
            new_constraints.extend_from_slice(&second_constraints[0..5]);
            new_constraints
        };

        constraints.extend(double_constraint(20, 125));
        constraints.extend(select_and_add_constraint(125, 115, 0, false));
        constraints.extend(select_and_add_constraint(115, 105, 5, true));

        constraints.extend(double_constraint(105, 95));
        constraints.extend(select_and_add_constraint(95, 85, 1, false));
        constraints.extend(select_and_add_constraint(85, 75, 6, true));

        constraints.extend(double_constraint(75, 65));
        constraints.extend(select_and_add_constraint(65, 55, 2, false));
        constraints.extend(select_and_add_constraint(55, 45, 7, true));



        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        _builder: &mut CircuitBuilder<GoldilocksField, D>,
        _vars: EvaluationTargets<'_, D>,
    ) -> Vec<ExtensionTarget<D>> {
        todo!();
    }

    fn generators(
        &self,
        row: usize,
        _local_constants: &[GoldilocksField],
    ) -> Vec<WitnessGeneratorRef<GoldilocksField, D>> {
        vec![WitnessGeneratorRef::new(ECAddXuGenerator { row }.adapter())]
    }

    fn num_wires(&self) -> usize {
        self.max_ops * Self::WIRES_PER_OP
    }

    fn degree(&self) -> usize {
        Self::DEGREE
    }

    fn num_ops(&self) -> usize {
        self.max_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn num_constraints(&self) -> usize {
        self.max_ops * Self::OUTPUTS_PER_OP
    }
}

#[cfg(test)]
mod test {
    use plonky2::{
        gates::gate_testing::{test_eval_fns, test_low_degree},
        plonk::{circuit_data::CircuitConfig, config::PoseidonGoldilocksConfig},
    };

    use crate::backends::plonky2::primitives::ec::gates::{
        curve::ECAddHomogOffset, generic::GateAdapter,
    };

    #[test]
    fn test_recursion() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = GateAdapter::<ECAddHomogOffset>::new_from_config(&config);

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(gate)
    }

    #[test]
    fn test_low_degree_orig() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = GateAdapter::<ECAddHomogOffset>::new_from_config(&config);

        test_low_degree::<_, _, 2>(gate);
        Ok(())
    }

    #[test]
    fn test_low_degree_recursive() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let orig_gate = GateAdapter::<ECAddHomogOffset>::new_from_config(&config);

        test_low_degree::<_, _, 2>(orig_gate.recursive_gate());
        Ok(())
    }

    #[test]
    fn test_double_recursion() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let orig_gate = GateAdapter::<ECAddHomogOffset>::new_from_config(&config);
        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(orig_gate.recursive_gate())
    }
}
