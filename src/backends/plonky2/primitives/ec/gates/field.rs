use std::{
    array,
    marker::PhantomData,
    ops::{Add, Mul, Neg, Range, Sub},
};

use itertools::zip_eq;
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

use crate::backends::plonky2::primitives::ec::curve::ECFieldExt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TensorProduct<const D1: usize, const D2: usize, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    pub components: [F2; D1],
    _phantom_data: PhantomData<F1>,
}

impl<const D1: usize, const D2: usize, F1, F2> TensorProduct<D1, D2, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    pub fn new(components: [F2; D1]) -> Self {
        Self {
            components,
            _phantom_data: PhantomData,
        }
    }

    pub fn add_base_field(self, rhs: F2::BaseField) -> Self {
        let mut c = self.components;
        let mut c2 = c[0].to_basefield_array();
        c2[0] += rhs;
        c[0] = F2::from_basefield_array(c2);
        Self::new(c)
    }

    pub fn add_one(self) -> Self {
        self.add_base_field(F2::BaseField::ONE)
    }

    pub fn mul_scalar(self, rhs: F2::BaseField) -> Self {
        Self::new(self.components.map(|x| x.scalar_mul(rhs)))
    }

    pub fn double(self) -> Self {
        self + self
    }

    pub fn is_zero(self) -> bool {
        self.components.iter().all(|x| x.is_zero())
    }
}

impl<const D1: usize, const D2: usize, F1, F2> Add<Self> for TensorProduct<D1, D2, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(array::from_fn(|i| self.components[i] + rhs.components[i]))
    }
}

impl<const D1: usize, const D2: usize, F1, F2> Mul<Self> for TensorProduct<D1, D2, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mut components = array::from_fn(|_| F2::ZERO);
        for i in 0..D1 {
            for j in 0..D1 {
                let prod = self.components[i] * rhs.components[j];
                if i + j < D1 {
                    components[i + j] += prod;
                } else {
                    components[i + j - D1] += prod.scalar_mul(F1::W)
                }
            }
        }
        Self::new(components)
    }
}

impl<const D1: usize, const D2: usize, F1, F2> Sub<Self> for TensorProduct<D1, D2, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(array::from_fn(|i| self.components[i] - rhs.components[i]))
    }
}

impl<const D1: usize, const D2: usize, F1, F2> Neg for TensorProduct<D1, D2, F1, F2>
where
    F1: OEF<D1>,
    F2: FieldExtension<D2, BaseField = F1::BaseField>,
{
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(self.components.map(|x| -x))
    }
}

pub(super) type QuinticTensor<const D: usize> = TensorProduct<
    5,
    D,
    QuinticExtension<GoldilocksField>,
    <GoldilocksField as Extendable<D>>::Extension,
>;

impl<const D: usize> ECFieldExt<D> for QuinticTensor<D>
where
    GoldilocksField: Extendable<D>,
{
    type Base = <GoldilocksField as Extendable<D>>::Extension;
    fn to_base(self) -> [Self::Base; 5] {
        self.components
    }
    fn from_base(components: [Self::Base; 5]) -> Self {
        Self::new(components)
    }
}

/// A gate which can perform a multiplication on OEF.
/// If the config has enough routed wires, it can support several such operations in one gate.
#[derive(Debug, Clone)]
pub struct NNFMulGate<const D: usize, const DEG: usize, NNF: OEF<DEG>> {
    /// Number of multiplications performed by the gate.
    pub num_ops: usize,
    _phantom_data: PhantomData<NNF>,
}

impl<const D: usize, const DEG: usize, NNF: OEF<DEG>> NNFMulGate<D, DEG, NNF> {
    pub const fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom_data: PhantomData,
        }
    }

    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 3 * DEG;
        config.num_routed_wires / wires_per_op
    }

    pub(crate) const fn wires_ith_multiplicand_0(i: usize) -> Range<usize> {
        3 * DEG * i..3 * DEG * i + DEG
    }
    pub(crate) const fn wires_ith_multiplicand_1(i: usize) -> Range<usize> {
        3 * DEG * i + DEG..3 * DEG * i + 2 * DEG
    }
    pub(crate) const fn wires_ith_output(i: usize) -> Range<usize> {
        3 * DEG * i + 2 * DEG..3 * DEG * (i + 1)
    }
}

impl<const D: usize, const DEG: usize, NNF: OEF<DEG>> Gate<NNF::BaseField, D>
    for NNFMulGate<D, DEG, NNF>
where
    NNF::BaseField: RichField + Extendable<D>,
{
    fn id(&self) -> String {
        format!("{self:?}")
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<NNF::BaseField, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.num_ops)
    }

    fn deserialize(
        src: &mut Buffer,
        _common_data: &CommonCircuitData<NNF::BaseField, D>,
    ) -> IoResult<Self> {
        let num_ops = src.read_usize()?;
        Ok(Self {
            num_ops,
            _phantom_data: PhantomData,
        })
    }

    fn eval_unfiltered(
        &self,
        vars: EvaluationVars<NNF::BaseField, D>,
    ) -> Vec<<NNF::BaseField as Extendable<D>>::Extension> {
        let mut constraints = Vec::with_capacity(self.num_ops * DEG);
        for i in 0..self.num_ops {
            let multiplicand_0: TensorProduct<DEG, D, NNF, _> = TensorProduct::new(
                vars.local_wires[Self::wires_ith_multiplicand_0(i)]
                    .try_into()
                    .unwrap(),
            );
            let multiplicand_1 = TensorProduct::new(
                vars.local_wires[Self::wires_ith_multiplicand_1(i)]
                    .try_into()
                    .unwrap(),
            );
            let output = TensorProduct::new(
                vars.local_wires[Self::wires_ith_output(i)]
                    .try_into()
                    .unwrap(),
            );
            let computed_output = multiplicand_0 * multiplicand_1;

            constraints.extend((output - computed_output).components);
        }

        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<NNF::BaseField, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut constraints = Vec::with_capacity(self.num_ops * DEG);
        for i in 0..self.num_ops {
            let multiplicand_0: [ExtensionTarget<D>; DEG] = vars.local_wires
                [Self::wires_ith_multiplicand_0(i)]
            .try_into()
            .unwrap();
            let multiplicand_1: [ExtensionTarget<D>; DEG] = vars.local_wires
                [Self::wires_ith_multiplicand_1(i)]
            .try_into()
            .unwrap();
            let output: [ExtensionTarget<D>; DEG] = vars.local_wires[Self::wires_ith_output(i)]
                .try_into()
                .unwrap();
            let computed_output =
                nnf_mul_ext::<_, DEG, NNF>(builder, &multiplicand_0, &multiplicand_1);

            let diffs = zip_eq(output, computed_output)
                .map(|(o, co)| builder.sub_extension(o, co))
                .collect::<Vec<_>>();
            constraints.extend(diffs);
        }

        constraints
    }

    fn generators(
        &self,
        row: usize,
        _local_constants: &[NNF::BaseField],
    ) -> Vec<WitnessGeneratorRef<NNF::BaseField, D>> {
        (0..self.num_ops)
            .map(|i| {
                WitnessGeneratorRef::new(
                    NNFMulGenerator::<D, DEG, NNF> {
                        row,
                        i,
                        phantom_data: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    fn num_wires(&self) -> usize {
        self.num_ops * 3 * DEG
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        3
    }

    fn num_constraints(&self) -> usize {
        self.num_ops * DEG
    }
}

#[derive(Clone, Debug, Default)]
pub struct NNFMulGenerator<const D: usize, const DEG: usize, NNF: OEF<DEG>> {
    row: usize,
    i: usize,
    phantom_data: PhantomData<NNF>,
}

impl<const D: usize, const DEG: usize, NNF: OEF<DEG>> SimpleGenerator<NNF::BaseField, D>
    for NNFMulGenerator<D, DEG, NNF>
where
    NNF::BaseField: RichField + Extendable<D>,
{
    fn id(&self) -> String {
        "NNFMulGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        NNFMulGate::<D, DEG, NNF>::wires_ith_multiplicand_0(self.i)
            .chain(NNFMulGate::<D, DEG, NNF>::wires_ith_multiplicand_1(self.i))
            .map(|i| Target::wire(self.row, i))
            .collect()
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<NNF::BaseField>,
        out_buffer: &mut GeneratedValues<NNF::BaseField>,
    ) -> anyhow::Result<()> {
        let extract_nnf = |range: Range<usize>| -> anyhow::Result<NNF> {
            let components: [NNF::BaseField; DEG] = range
                .map(|i| witness.get_target(Target::wire(self.row, i)))
                .collect::<Vec<_>>()
                .try_into()
                .map_err(|e| anyhow::anyhow!("{:?}", e))?;
            Ok(NNF::from_basefield_array(components))
        };

        let multiplicand_0 =
            extract_nnf(NNFMulGate::<D, DEG, NNF>::wires_ith_multiplicand_0(self.i))?;
        let multiplicand_1 =
            extract_nnf(NNFMulGate::<D, DEG, NNF>::wires_ith_multiplicand_1(self.i))?;

        let output_targets: [Target; DEG] = NNFMulGate::<D, DEG, NNF>::wires_ith_output(self.i)
            .map(|i| Target::wire(self.row, i))
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|e| anyhow::anyhow!("{:?}", e))?;

        let computed_output = multiplicand_0 * multiplicand_1;

        out_buffer.set_target_arr(&output_targets, &computed_output.to_basefield_array())
    }

    fn serialize(
        &self,
        dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<NNF::BaseField, D>,
    ) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)
    }

    fn deserialize(
        src: &mut Buffer,
        _common_data: &CommonCircuitData<NNF::BaseField, D>,
    ) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        Ok(Self {
            row,
            i,
            phantom_data: PhantomData,
        })
    }
}

pub(crate) fn nnf_mul_ext<const D: usize, const DEG: usize, NNF: OEF<DEG>>(
    builder: &mut CircuitBuilder<NNF::BaseField, D>,
    x: &[ExtensionTarget<D>; DEG],
    y: &[ExtensionTarget<D>; DEG],
) -> [ExtensionTarget<D>; DEG]
where
    NNF::BaseField: RichField + Extendable<D>,
{
    let zero = builder.zero_extension();
    let mul_targets = (0..DEG - 1)
        .map(|k| {
            let term1 = (0..=k)
                .map(|i| builder.mul_extension(x[i], y[k - i]))
                .collect::<Vec<_>>()
                .into_iter()
                .reduce(|sum, summand| builder.add_extension(sum, summand))
                .expect("Missing summands");
            let term2 = (k + 1..DEG)
                .map(|i| {
                    builder.arithmetic_extension(
                        NNF::W,
                        NNF::BaseField::ZERO,
                        x[i],
                        y[DEG + k - i],
                        zero,
                    )
                })
                .collect::<Vec<_>>()
                .into_iter()
                .reduce(|sum, summand| builder.add_extension(sum, summand))
                .expect("Missing summands");
            builder.add_extension(term1, term2)
        })
        .collect::<Vec<_>>()
        .into_iter()
        .chain(std::iter::once(
            (0..DEG)
                .map(|i| builder.mul_extension(x[i], y[DEG - 1 - i]))
                .collect::<Vec<_>>()
                .into_iter()
                .reduce(|sum, summand| builder.add_extension(sum, summand))
                .expect("Missing summands"),
        ))
        .collect::<Vec<_>>();
    std::array::from_fn(|i| mul_targets[i])
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{extension::quintic::QuinticExtension, goldilocks_field::GoldilocksField},
        gates::gate_testing::{test_eval_fns, test_low_degree},
        plonk::{circuit_data::CircuitConfig, config::PoseidonGoldilocksConfig},
    };

    use crate::backends::plonky2::{basetypes::D, primitives::ec::gates::field::NNFMulGate};

    #[test]
    fn test_nnf_mul_gate() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = NNFMulGate::<D, 5, QuinticExtension<GoldilocksField>>::new_from_config(&config);

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(gate)
    }

    #[test]
    fn test_nnf_mul_gate_low_degree() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate = NNFMulGate::<D, 5, QuinticExtension<GoldilocksField>>::new_from_config(&config);

        test_low_degree::<_, _, 2>(gate);
        Ok(())
    }
}
