/// This file contains the RecursiveCircuit, the circuit used for recursion.
///
/// The RecursiveCircuit verifies N proofs of itself (N=arity), together with
/// the logic defined at the InnerCircuit (in our case, used for the
/// MainPodCircuit logic).
///
/// The arity defines the maximum amount of proofs of itself that the
/// RecursiveCircuit verifies. When arity>1, using the RecursiveCircuit has the
/// shape of a tree of the same arity.
///                                              
//
//                      π_root
//                        ▲
//                ┌───────┴────────┐
//                │RecursiveCircuit│
//                └─▲───▲───▲────▲─┘
//          ┌───────┘  ┌┘   └┐   └──────┐
//          │π''_1     │ ... │     π''_N│
// ┌────────┴───────┐ ┌┴┐┌─┐┌┴┐ ┌───────┴────────┐
// │RecursiveCircuit│ │.││.││.│ │RecursiveCircuit│
// └──▲─────────▲───┘ └─┘└─┘└─┘ └──▲─────────▲───┘
//    │         │                  │         │
//   π_1  ...  π_N               π'_1 ...  π'_N
//
//
// where
// N: arity of the RecursiveCircuit
// π_i: plonky2 proof of the RecursiveCircuit
//
use hashbrown::HashMap;
use plonky2::{
    self,
    gates::noop::NoopGate,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, ProverCircuitData, VerifierCircuitData,
            VerifierCircuitTarget,
        },
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    recursion::dummy_circuit::cyclic_base_proof,
};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, C, D},
        error::{Error, Result},
    },
    middleware::F,
};

/// InnerCircuit is the trait used to define the logic of the circuit that is
/// computed inside the RecursiveCircuit.
pub trait InnerCircuit: Clone {
    type Input;
    type Params;

    fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &Self::Params,
        // public_inputs will be used for the recursive proof verification
        public_inputs: Vec<Target>,
        selectors: Vec<BoolTarget>,
    ) -> Result<Self>;

    /// assigns the values to the targets
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()>;
}

#[derive(Clone, Debug)]
pub struct RecursiveParams {
    /// determines the arity of the RecursiveCircuit
    arity: usize,
}

/// RecursiveCircuit defines the circuit that verifies `arity` proofs of itself.
pub struct RecursiveCircuit<I: InnerCircuit> {
    params: RecursiveParams,
    selectors_targ: Vec<BoolTarget>,
    innercircuit_targ: I,
    proofs_targ: Vec<ProofWithPublicInputsTarget<D>>,
    // cyclic-recursion params:
    verifier_data_targ: VerifierCircuitTarget,
    verifier_data: VerifierCircuitData<F, C, D>,
}

impl<I: InnerCircuit> RecursiveCircuit<I> {
    pub fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &RecursiveParams,
        inner_params: &I::Params,
        // self's verifier_data
        verifier_data: VerifierCircuitData<F, C, D>,
    ) -> Result<Self> {
        let selectors_targ: Vec<BoolTarget> = (0..params.arity)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();

        // proof verification
        let common_data = verifier_data.common.clone();
        let verifier_data_targ = builder.add_verifier_data_public_inputs();
        let proofs_targ: Result<Vec<ProofWithPublicInputsTarget<D>>> = (0..params.arity)
            .map(|i| {
                let proof_targ = builder.add_virtual_proof_with_pis(&common_data);
                builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
                    selectors_targ[i],
                    &proof_targ,
                    &common_data,
                )?;
                Ok(proof_targ)
            })
            .collect();
        let proofs_targ = proofs_targ?;

        // get the targets of the public inputs used to verify the proofs, to be
        // used in the InnerCircuit
        let pub_inp: Vec<Target> = proofs_targ
            .iter()
            .flat_map(|proof_pis| proof_pis.public_inputs.clone())
            .collect();

        // build the InnerCircuits logic
        let innercircuit_targ: I =
            I::build(builder, inner_params, pub_inp, selectors_targ.clone())?;

        Ok(Self {
            params: params.clone(),
            selectors_targ,
            innercircuit_targ,
            proofs_targ,
            verifier_data_targ,
            verifier_data,
        })
    }

    pub fn set_targets(
        &mut self,
        pw: &mut PartialWitness<F>,
        dummy_proof: Proof,
        innercircuit_input: I::Input,
        recursive_proofs: Vec<Proof>,
    ) -> Result<()> {
        let n = recursive_proofs.len();
        assert!(n <= self.params.arity);

        // fill the missing proofs with dummy_proofs
        let dummy_proofs: Vec<Proof> = (n..self.params.arity)
            .map(|_| dummy_proof.clone())
            .collect();
        let recursive_proofs: Vec<Proof> = [recursive_proofs, dummy_proofs].concat();

        // set the first n selectors to true, and the rest to false
        for i in 0..n {
            pw.set_bool_target(self.selectors_targ[i], true)?;
        }
        for i in n..self.params.arity {
            pw.set_bool_target(self.selectors_targ[i], false)?;
        }

        // set the InnerCircuit related values
        self.innercircuit_targ
            .set_targets(pw, &innercircuit_input)?;

        // recursive proofs verification
        pw.set_verifier_data_target(&self.verifier_data_targ, &self.verifier_data.verifier_only)?;

        #[allow(clippy::needless_range_loop)]
        for i in 0..self.params.arity {
            // put together the public inputs with the verifier_data. Note:
            // current version doesn't use InnerCircuit's public inputs (vec![])
            let public_inputs = Self::prepare_public_inputs(vec![], self.verifier_data.clone());

            pw.set_proof_with_pis_target(
                &self.proofs_targ[i],
                &ProofWithPublicInputs {
                    proof: recursive_proofs[i].clone(),
                    public_inputs: public_inputs.clone(),
                },
            )?;
        }

        Ok(())
    }

    /// returns the full-recursive CircuitData
    pub fn circuit_data(
        params: &RecursiveParams,
        inner_params: &I::Params,
    ) -> Result<CircuitData<F, C, D>> {
        let mut data = common_data_for_recursion::<I>(params, inner_params)?;

        // build the actual RecursiveCircuit circuit data
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build(&mut builder, params, inner_params, data.verifier_data())?;
        data = builder.build::<C>();

        Ok(data)
    }

    /// returns ProverCircuitData
    pub fn build_prover(
        params: &RecursiveParams,
        inner_params: &I::Params,
        verifier_data: VerifierCircuitData<F, C, D>,
    ) -> Result<ProverCircuitData<F, C, D>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build(&mut builder, params, inner_params, verifier_data.clone())?;

        Ok(builder.build_prover::<C>())
    }

    pub fn dummy_proof(circuit_data: CircuitData<F, C, D>) -> Proof {
        let verifier_data = circuit_data.verifier_data();
        let dummy_proof_pis = cyclic_base_proof(
            &circuit_data.common,
            &verifier_data.verifier_only,
            HashMap::new(),
        );
        dummy_proof_pis.proof
    }

    pub fn prepare_public_inputs(
        public_inputs: Vec<F>,
        verifier_data: VerifierCircuitData<F, C, D>,
    ) -> Vec<F> {
        [
            public_inputs,
            // add verifier_data
            verifier_data.verifier_only.circuit_digest.elements.to_vec(),
            verifier_data
                .verifier_only
                .constants_sigmas_cap
                .0
                .iter()
                .flat_map(|e| e.elements)
                .collect(),
        ]
        .concat()
    }
}

fn common_data_for_recursion<I: InnerCircuit>(
    params: &RecursiveParams,
    inner_params: &I::Params,
) -> Result<CircuitData<F, C, D>> {
    // 1st
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();

    // 2nd
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    // proofs
    for _ in 0..params.arity {
        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    }
    let data = builder.build::<C>();

    // 3rd
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    builder.add_gate(
        // add a ConstantGate, because without this, when later generating the `dummy_circuit`
        // (inside the `conditionally_verify_cyclic_proof_or_dummy`), it fails due the
        // `CommonCircuitData` of the generated circuit not matching the given `CommonCircuitData`
        // to create it. Without this it fails because it misses a ConstantGate.
        plonky2::gates::constant::ConstantGate::new(config.num_constants),
        vec![],
    );

    // set the targets for the InnerCircuit
    let _ = I::build(&mut builder, inner_params, vec![], vec![])?;

    // cyclic_recursion proofs
    let verifier_data = builder.add_verifier_data_public_inputs();
    for _ in 0..params.arity {
        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    }

    // pad min gates
    let n_gates = compute_num_gates(params)?;
    while builder.num_gates() < n_gates {
        builder.add_gate(NoopGate, vec![]);
    }
    Ok(builder.build::<C>())
}

fn compute_num_gates(params: &RecursiveParams) -> Result<usize> {
    // Note: the following numbers are WIP, obtained by trial-error by running different
    // configurations in the tests.
    let n_gates = match params.arity {
        0..=1 => 1 << 12,
        2 => 1 << 13,
        3..=5 => 1 << 14,
        6 => 1 << 15,
        _ => 0,
    };
    if n_gates == 0 {
        return Err(Error::custom(format!(
            "arity={} not supported. Currently supported arity from 1 to 6 (both included)",
            params.arity
        )));
    }
    Ok(n_gates)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use plonky2::{
        field::types::Field,
        hash::{
            hash_types::{HashOut, HashOutTarget},
            poseidon::PoseidonHash,
        },
        plonk::config::Hasher,
    };

    use super::*;

    // out-of-circuit input-output computation for Circuit1
    fn circuit1_io(inp: HashOut<F>) -> HashOut<F> {
        let mut out: HashOut<F> = inp;
        for _ in 0..100 {
            out = PoseidonHash::hash_no_pad(&out.elements)
        }
        out
    }
    // out-of-circuit input-output computation for Circuit2
    fn circuit2_io(inp: HashOut<F>) -> HashOut<F> {
        let mut out: HashOut<F> = inp;
        for _ in 0..2000 {
            out = PoseidonHash::hash_no_pad(&out.elements)
        }
        out
    }
    // out-of-circuit input-output computation for Circuit3
    fn circuit3_io(inp: HashOut<F>) -> HashOut<F> {
        let mut aux: F = inp.elements[0];
        let two = F::from_canonical_u64(2u64);
        for _ in 0..10_000 {
            aux = aux + two;
        }
        HashOut::<F>::from_vec(vec![aux, F::ZERO, F::ZERO, F::ZERO])
    }
    #[derive(Clone, Debug)]
    pub struct Circuit1 {
        input: HashOutTarget,
        output: HashOutTarget,
    }
    impl InnerCircuit for Circuit1 {
        type Input = (HashOut<F>, HashOut<F>); // (input, output)
        type Params = ();
        fn build(
            builder: &mut CircuitBuilder<F, D>,
            _params: &Self::Params,
            _public_inputs: Vec<Target>,
            _selectors: Vec<BoolTarget>,
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();

            let mut output_targ: HashOutTarget = input_targ.clone();
            for _ in 0..100 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            Ok(Self {
                input: input_targ,
                output: output_targ,
            })
        }
        fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()> {
            pw.set_hash_target(self.input, input.0)?;
            pw.set_hash_target(self.output, input.1)?;
            Ok(())
        }
    }
    #[derive(Clone, Debug)]
    pub struct Circuit2 {
        input: HashOutTarget,
        output: HashOutTarget,
    }
    impl InnerCircuit for Circuit2 {
        type Input = (HashOut<F>, HashOut<F>); // (input, output)
        type Params = ();
        fn build(
            builder: &mut CircuitBuilder<F, D>,
            _params: &Self::Params,
            _public_inputs: Vec<Target>,
            _selectors: Vec<BoolTarget>,
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();

            let mut output_targ: HashOutTarget = input_targ.clone();
            for _ in 0..2000 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            Ok(Self {
                input: input_targ,
                output: output_targ,
            })
        }
        fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()> {
            pw.set_hash_target(self.input, input.0)?;
            pw.set_hash_target(self.output, input.1)?;
            Ok(())
        }
    }
    #[derive(Clone, Debug)]
    pub struct Circuit3 {
        input: HashOutTarget,
        output: HashOutTarget,
    }
    impl InnerCircuit for Circuit3 {
        type Input = (HashOut<F>, HashOut<F>); // (input, output)
        type Params = ();
        fn build(
            builder: &mut CircuitBuilder<F, D>,
            _params: &Self::Params,
            _public_inputs: Vec<Target>,
            _selectors: Vec<BoolTarget>,
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();
            let mut aux: Target = input_targ.elements[0];
            let two = builder.constant(F::from_canonical_u64(2u64));
            for _ in 0..10_000 {
                aux = builder.add(aux, two);
            }
            let zero = builder.zero();
            let output_targ = HashOutTarget::from_vec(vec![aux, zero, zero, zero]);

            Ok(Self {
                input: input_targ,
                output: output_targ,
            })
        }
        fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()> {
            pw.set_hash_target(self.input, input.0)?;
            pw.set_hash_target(self.output, input.1)?;
            Ok(())
        }
    }

    #[test]
    fn test_circuit_i() -> Result<()> {
        let inner_params = ();
        let inp = HashOut::<F>::ZERO;

        let inner_inputs = (inp, circuit1_io(inp));
        test_circuit_i_opt::<Circuit1>(&inner_params, inner_inputs)?;

        let inner_inputs = (inp, circuit2_io(inp));
        test_circuit_i_opt::<Circuit2>(&inner_params, inner_inputs)?;

        let inner_inputs = (inp, circuit3_io(inp));
        test_circuit_i_opt::<Circuit3>(&inner_params, inner_inputs)?;

        Ok(())
    }
    fn test_circuit_i_opt<IC: InnerCircuit>(
        inner_params: &IC::Params,
        inner_inputs: IC::Input,
    ) -> Result<()> {
        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = IC::build(&mut builder, inner_params, vec![], vec![])?;
        targets.set_targets(&mut pw, &inner_inputs)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    fn test_recursive_circuit_opt(
        // arity: number of cyclic recursion proofs verified at each node of the
        // recursion tree
        arity: usize,
        // n_steps: determines the number of recursive steps. Notice that when
        // arity>1, n_steps determines the number of levels of the recursive
        // tree
        n_steps: usize,
    ) -> Result<()> {
        let params = RecursiveParams { arity };

        type RC<I> = RecursiveCircuit<I>;
        let inner_params = ();

        // build the circuit_data & verifier_data for the recursive circuit
        let start = Instant::now();
        let circuit_data = RC::<Circuit1>::circuit_data(&params, &inner_params)?;
        let verifier_data = circuit_data.verifier_data();
        let prover = RC::<Circuit1>::build_prover(&params, &inner_params, verifier_data.clone())?;
        let dummy_proof = RC::<Circuit1>::dummy_proof(circuit_data);
        println!(
            "circuit_data,prover,dummy_proof generated {:?}",
            start.elapsed()
        );

        // build 1st circuit: circuit1, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit1
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config.clone());
        let mut circuit = RC::<Circuit1>::build(&mut builder, &params, &(), verifier_data.clone())?;
        println!("Circuit1 num_gates {}", builder.num_gates());

        // build 2nd circuit: circuit2, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit2
        let mut builder2 = CircuitBuilder::new(config.clone());
        let mut circuit2 =
            RC::<Circuit2>::build(&mut builder2, &params, &(), verifier_data.clone())?;
        println!("Circuit2 num_gates {}", builder2.num_gates());

        // build 3rd circuit: circuit3, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit3
        let mut builder3 = CircuitBuilder::new(config);
        let mut circuit3 =
            RC::<Circuit3>::build(&mut builder3, &params, &(), verifier_data.clone())?;
        println!("Circuit3 num_gates {}", builder3.num_gates());

        // we start with 0 proofs at the first iteration, which means that
        // internally at RecursiveCircuit.set_targets, it will use all
        // dummy_proofs
        let mut proofs_at_level_i: Vec<Proof> = vec![];

        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));

        // loop over the recursion steps
        for i in 0..n_steps {
            let mut next_level_proofs: Vec<Proof> = vec![];

            // loop over the nodes of each recursion tree level
            for j in 0..arity {
                // do the recursive step
                let start = Instant::now();
                let mut pw = PartialWitness::new();
                circuit.set_targets(
                    &mut pw,
                    dummy_proof.clone(),
                    inner_inputs,              // innercircuit_input
                    proofs_at_level_i.clone(), // recursive_proofs
                )?;
                let new_proof = prover.prove(pw)?.proof;
                println!(
                    "RecursiveTree::prove_node (level: i={}, node: j={}) took: {:?}ms",
                    i,
                    j,
                    start.elapsed()
                );

                // verify the recursive proof
                let public_inputs =
                    RC::<Circuit1>::prepare_public_inputs(vec![], verifier_data.clone());
                verifier_data.clone().verify(ProofWithPublicInputs {
                    proof: new_proof.clone(),
                    public_inputs: public_inputs.clone(),
                })?;

                // set new_proof for next iteration
                next_level_proofs.push(new_proof);
            }
            proofs_at_level_i = next_level_proofs.clone();
        }

        // do one more iteration, but now with Circuit2
        let inner_inputs = (inp, circuit2_io(inp));
        let mut pw = PartialWitness::new();
        circuit2.set_targets(
            &mut pw,
            dummy_proof.clone(),
            inner_inputs,              // innercircuit_input
            proofs_at_level_i.clone(), // recursive_proofs
        )?;
        let new_proof = prover.prove(pw)?.proof;
        let public_inputs = RC::<Circuit2>::prepare_public_inputs(vec![], verifier_data.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data.clone().verify(ProofWithPublicInputs {
            proof: new_proof.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // do another final iteration, now with Circuit3
        let inner_inputs = (inp, circuit3_io(inp));
        let mut pw = PartialWitness::new();
        circuit3.set_targets(
            &mut pw,
            dummy_proof.clone(),
            inner_inputs,    // innercircuit_input
            vec![new_proof], // recursive_proofs
        )?;
        let new_proof = prover.prove(pw)?.proof;
        let public_inputs = RC::<Circuit3>::prepare_public_inputs(vec![], verifier_data.clone());
        verifier_data.clone().verify(ProofWithPublicInputs {
            proof: new_proof.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // verify the last proof
        let public_inputs = RC::<Circuit3>::prepare_public_inputs(vec![], verifier_data.clone());
        let pis = ProofWithPublicInputs {
            proof: new_proof.clone(),
            public_inputs: public_inputs.clone(),
        };
        verifier_data.clone().verify(pis.clone())?;

        Ok(())
    }

    #[test]
    fn test_recursive_circuit() -> Result<()> {
        // arity=1, n_steps=4
        // test_recursive_circuit_opt(1, 4)?;

        // arity=2, n_steps=3
        test_recursive_circuit_opt(2, 3)?; // commented to be skipped in the CI since it's slower

        Ok(())
    }
}
