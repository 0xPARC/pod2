use plonky2::field::goldilocks_field::GoldilocksField;

use crate::backends::plonky2::primitives::ec::{
    curve::{double_homog, mixed_add, ECFieldExt},
    gates::{field::QuinticTensor, generic::SimpleGate},
};

/// Gate computing the addition of two elliptic curve points, one in
/// affine and one in fractional/homogeneous coordinates.
#[derive(Debug, Clone)]
pub struct ECAddMixed;

impl SimpleGate for ECAddMixed {
    type F = GoldilocksField;
    const INPUTS_PER_OP: usize = 30;
    const OUTPUTS_PER_OP: usize = 20;
    const DEGREE: usize = 6;
    const ID: &'static str = "ECAddMixed";
    fn eval<const D: usize>(
        wires: &[<Self::F as plonky2::field::extension::Extendable<D>>::Extension],
    ) -> Vec<<Self::F as plonky2::field::extension::Extendable<D>>::Extension>
    where
        Self::F: plonky2::field::extension::Extendable<D>,
    {
        let mut ans = Vec::with_capacity(20);
        let x1 = QuinticTensor::from_base(wires[0..5].try_into().unwrap());
        let z1 = QuinticTensor::from_base(wires[5..10].try_into().unwrap());
        let u1 = QuinticTensor::from_base(wires[10..15].try_into().unwrap());
        let t1 = QuinticTensor::from_base(wires[15..20].try_into().unwrap());
        let x2 = QuinticTensor::from_base(wires[20..25].try_into().unwrap());
        let u2 = QuinticTensor::from_base(wires[25..30].try_into().unwrap());

        let out = mixed_add(x1, z1, u1, t1, x2, u2);
        for v in out {
            ans.extend(v.to_base());
        }
        ans
    }
}

/// Gate computing the doubling of a point in fractional/homogeneous
/// coordinates.
#[derive(Debug, Clone)]
pub struct ECDblHomog;

impl SimpleGate for ECDblHomog {
    type F = GoldilocksField;
    const INPUTS_PER_OP: usize = 20;
    const OUTPUTS_PER_OP: usize = 20;
    const DEGREE: usize = 6;
    const ID: &'static str = "ECDblHomog";
    fn eval<const D: usize>(
        wires: &[<Self::F as plonky2::field::extension::Extendable<D>>::Extension],
    ) -> Vec<<Self::F as plonky2::field::extension::Extendable<D>>::Extension>
    where
        Self::F: plonky2::field::extension::Extendable<D>,
    {
        let mut ans = Vec::with_capacity(20);
        let x = QuinticTensor::from_base(wires[0..5].try_into().unwrap());
        let z = QuinticTensor::from_base(wires[5..10].try_into().unwrap());
        let u = QuinticTensor::from_base(wires[10..15].try_into().unwrap());
        let t = QuinticTensor::from_base(wires[15..20].try_into().unwrap());

        let out = double_homog(x, z, u, t);
        for v in out {
            ans.extend(v.to_base());
        }
        ans
    }
}

#[cfg(test)]
mod test {
    use plonky2::{
        field::{
            extension::{Extendable, FieldExtension},
            types::Sample,
        },
        gates::{gate::Gate, gate_testing::test_low_degree},
        hash::hash_types::{HashOut, RichField},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
            vars::{EvaluationTargets, EvaluationVars, EvaluationVarsBaseBatch},
        },
    };

    use crate::backends::plonky2::{
        primitives::ec::gates::{
            curve::{ECAddMixed, ECDblHomog},
            generic::GateAdapter,
        },
        recursion::circuit::std_config,
    };

    #[test]
    fn test_recursion() -> Result<(), anyhow::Error> {
        let config = std_config();
        let gate1 = GateAdapter::<ECAddMixed>::new_from_config(&config);
        let gate2 = GateAdapter::<ECDblHomog>::new_from_config(&config);

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(config.clone(), gate1)?;
        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(config, gate2)
    }

    #[test]
    fn test_low_degree_orig() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate1 = GateAdapter::<ECAddMixed>::new_from_config(&config);
        let gate2 = GateAdapter::<ECDblHomog>::new_from_config(&config);

        test_low_degree::<_, _, 2>(gate1);
        test_low_degree::<_, _, 2>(gate2);
        Ok(())
    }

    #[test]
    fn test_low_degree_recursive() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate1 = GateAdapter::<ECAddMixed>::new_from_config(&config);
        let gate2 = GateAdapter::<ECDblHomog>::new_from_config(&config);

        test_low_degree::<_, _, 2>(gate1.recursive_gate());
        test_low_degree::<_, _, 2>(gate2.recursive_gate());
        Ok(())
    }

    #[test]
    fn test_double_recursion() -> Result<(), anyhow::Error> {
        let config = CircuitConfig::standard_recursion_config();
        let gate1 = GateAdapter::<ECAddMixed>::new_from_config(&config);
        let gate2 = GateAdapter::<ECDblHomog>::new_from_config(&config);

        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(config.clone(), gate1.recursive_gate())?;
        test_eval_fns::<_, PoseidonGoldilocksConfig, _, 2>(config, gate2.recursive_gate())
    }

    // Adapted from plonky2::gates::gate_testing::test_eval_fns
    pub fn test_eval_fns<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        G: Gate<F, D>,
        const D: usize,
    >(
        config: CircuitConfig,
        gate: G,
    ) -> anyhow::Result<()> {
        // Test that `eval_unfiltered` and `eval_unfiltered_base` are coherent.
        let wires_base = F::rand_vec(gate.num_wires());
        let constants_base = F::rand_vec(gate.num_constants());
        let wires = wires_base
            .iter()
            .map(|&x| F::Extension::from_basefield(x))
            .collect::<Vec<_>>();
        let constants = constants_base
            .iter()
            .map(|&x| F::Extension::from_basefield(x))
            .collect::<Vec<_>>();
        let public_inputs_hash = HashOut::rand();

        // Batch of 1.
        let vars_base_batch =
            EvaluationVarsBaseBatch::new(1, &constants_base, &wires_base, &public_inputs_hash);
        let vars = EvaluationVars {
            local_constants: &constants,
            local_wires: &wires,
            public_inputs_hash: &public_inputs_hash,
        };

        let evals_base = gate.eval_unfiltered_base_batch(vars_base_batch);
        let evals = gate.eval_unfiltered(vars);
        // This works because we have a batch of 1.
        anyhow::ensure!(
            evals
                == evals_base
                    .into_iter()
                    .map(F::Extension::from_basefield)
                    .collect::<Vec<_>>()
        );

        // Test that `eval_unfiltered` and `eval_unfiltered_recursively` are coherent.
        let wires = F::Extension::rand_vec(gate.num_wires());
        let constants = F::Extension::rand_vec(gate.num_constants());

        let mut pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let wires_t = builder.add_virtual_extension_targets(wires.len());
        let constants_t = builder.add_virtual_extension_targets(constants.len());
        pw.set_extension_targets(&wires_t, &wires)?;
        pw.set_extension_targets(&constants_t, &constants)?;
        let public_inputs_hash_t = builder.add_virtual_hash();
        pw.set_hash_target(public_inputs_hash_t, public_inputs_hash)?;

        let vars = EvaluationVars {
            local_constants: &constants,
            local_wires: &wires,
            public_inputs_hash: &public_inputs_hash,
        };
        let evals = gate.eval_unfiltered(vars);

        let vars_t = EvaluationTargets {
            local_constants: &constants_t,
            local_wires: &wires_t,
            public_inputs_hash: &public_inputs_hash_t,
        };
        let evals_t = gate.eval_unfiltered_circuit(&mut builder, vars_t);
        pw.set_extension_targets(&evals_t, &evals)?;

        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }
}
