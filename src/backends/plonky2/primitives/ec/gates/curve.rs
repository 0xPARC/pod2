use plonky2::field::goldilocks_field::GoldilocksField;

use crate::backends::plonky2::primitives::ec::{
    curve::{add_homog_offset, ECFieldExt},
    gates::{field::QuinticTensor, generic::SimpleGate},
};

/// Gate computing the addition of two elliptic curve points in
/// homogeneous coordinates *minus* an offset in the `z` and `t`
/// coordinates, viz. the extension field generator times `Point::B1`,
/// cf. CircuitBuilderElliptic::add_point.
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
