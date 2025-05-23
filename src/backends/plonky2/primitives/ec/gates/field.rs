use std::{
    array,
    marker::PhantomData,
    ops::{Add, Mul, Neg, Sub},
};

use plonky2::{
    field::{
        extension::{quintic::QuinticExtension, Extendable, FieldExtension, OEF},
        goldilocks_field::GoldilocksField,
        types::Field,
    },
    hash::hash_types::RichField,
};

use crate::backends::plonky2::primitives::ec::{curve::ECFieldExt, gates::generic::SimpleGate};

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

#[derive(Debug, Clone, Copy, Default)]
pub struct NNFMulSimple<const DEG: usize, NNF: OEF<DEG>> {
    _phantom_data: PhantomData<fn(NNF) -> NNF>,
}

impl<const DEG: usize, NNF: OEF<DEG>> NNFMulSimple<DEG, NNF> {
    pub fn new() -> Self {
        Self {
            _phantom_data: PhantomData,
        }
    }
}

impl<NNF, const NNF_DEG: usize> SimpleGate for NNFMulSimple<NNF_DEG, NNF>
where
    NNF: OEF<NNF_DEG>,
    NNF::BaseField: RichField + Extendable<1>,
{
    type F = NNF::BaseField;
    const INPUTS_PER_OP: usize = 2 * NNF_DEG;
    const OUTPUTS_PER_OP: usize = NNF_DEG;
    const DEGREE: usize = 2;
    const ID: &'static str = "NNFSimpleGate";

    fn eval<const D: usize>(
        wires: &[<Self::F as Extendable<D>>::Extension],
    ) -> Vec<<Self::F as Extendable<D>>::Extension>
    where
        Self::F: Extendable<D>,
    {
        let x: TensorProduct<NNF_DEG, D, NNF, <Self::F as Extendable<D>>::Extension> =
            TensorProduct::new(array::from_fn(|i| wires[i]));
        let y = TensorProduct::new(array::from_fn(|i| wires[NNF_DEG + i]));
        let prod = x * y;
        prod.components.into()
    }
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{extension::quintic::QuinticExtension, goldilocks_field::GoldilocksField},
        gates::gate_testing::{test_eval_fns, test_low_degree},
        plonk::{circuit_data::CircuitConfig, config::PoseidonGoldilocksConfig},
    };

    use crate::backends::plonky2::primitives::ec::gates::{
        field::NNFMulSimple, generic::GateAdapter,
    };

    #[test]
    fn test_recursion() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate =
            GateAdapter::<NNFMulSimple<5, QuinticExtension<GoldilocksField>>>::new_from_config(
                &config,
            );

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(gate)
    }

    #[test]
    fn test_low_degree_orig() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate =
            GateAdapter::<NNFMulSimple<5, QuinticExtension<GoldilocksField>>>::new_from_config(
                &config,
            );

        test_low_degree::<_, _, 2>(gate);
        Ok(())
    }

    #[test]
    fn test_low_degree_recursive() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let orig_gate =
            GateAdapter::<NNFMulSimple<5, QuinticExtension<GoldilocksField>>>::new_from_config(
                &config,
            );

        test_low_degree::<_, _, 2>(orig_gate.recursive_gate());
        Ok(())
    }

    #[test]
    fn test_double_recursion() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let orig_gate =
            GateAdapter::<NNFMulSimple<5, QuinticExtension<GoldilocksField>>>::new_from_config(
                &config,
            );
        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(orig_gate.recursive_gate())
    }
}
