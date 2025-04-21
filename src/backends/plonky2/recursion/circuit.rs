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
use anyhow::{anyhow, Result};
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
    backends::plonky2::basetypes::{Proof, C, D},
    middleware::F,
};

/// InnerCircuit is the trait that is used to define the logic of the circuit
/// that is used inside the RecursiveCircuit.
pub trait InnerCircuit: Clone {
    type Targets;
    type Input;

    fn build(
        builder: &mut CircuitBuilder<F, D>,
        // public_inputs will be used for the recursive proof verification
        public_inputs: Vec<Target>,
        selectors: Vec<BoolTarget>,
    ) -> Result<Self::Targets>;

    fn set_targets(
        pw: &mut PartialWitness<F>,
        targets: &Self::Targets,
        input: &Self::Input,
    ) -> Result<Vec<F>>;
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
    innercircuit_targ: I::Targets,
    proofs_targ: Vec<ProofWithPublicInputsTarget<D>>,
    // cyclic-recursion params:
    verifier_data_targ: VerifierCircuitTarget,
    verifier_data: VerifierCircuitData<F, C, D>,
}

impl<I: InnerCircuit> RecursiveCircuit<I> {
    pub fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &RecursiveParams,
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
        let innercircuit_targ: I::Targets = I::build(builder, pub_inp, selectors_targ.clone())?;

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
        non_base_node: bool,
    ) -> Result<()> {
        let n = recursive_proofs.len();
        assert!(n <= self.params.arity);

        // fill the missing proofs with dummy_proofs
        let dummy_proofs: Vec<Proof> = (n..self.params.arity)
            .map(|_| dummy_proof.clone())
            .collect();
        let recursive_proofs: Vec<Proof> = [recursive_proofs, dummy_proofs].concat();

        // set the first n selectors to `non_base_node`, and the rest to false
        for i in 0..n {
            pw.set_bool_target(self.selectors_targ[i], non_base_node)?;
        }
        for i in n..self.params.arity {
            pw.set_bool_target(self.selectors_targ[i], false)?;
        }

        // set the InnerCircuit related values
        let innercircuit_pubinp: Vec<F> =
            I::set_targets(pw, &self.innercircuit_targ, &innercircuit_input)?;

        // recursive proofs verification
        pw.set_verifier_data_target(&self.verifier_data_targ, &self.verifier_data.verifier_only)?;

        // put together the public inputs with the verifier_data
        let public_inputs =
            Self::prepare_public_inputs(innercircuit_pubinp, self.verifier_data.clone());
        #[allow(clippy::needless_range_loop)]
        for i in 0..self.params.arity {
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
    pub fn circuit_data(params: &RecursiveParams) -> Result<CircuitData<F, C, D>> {
        let mut data = common_data_for_recursion::<I>(params)?;

        // build the actual RecursiveCircuit circuit data
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build(&mut builder, params, data.verifier_data())?;
        dbg!(builder.num_gates());
        data = builder.build::<C>();

        Ok(data)
    }

    /// returns ProverCircuitData
    pub fn build_prover(
        params: &RecursiveParams,
        verifier_data: VerifierCircuitData<F, C, D>,
    ) -> Result<ProverCircuitData<F, C, D>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build(&mut builder, params, verifier_data.clone())?;

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
    let _ = I::build(&mut builder, vec![], vec![])?;

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
        return Err(anyhow!(
            "arity={} not supported. Currently supported arity from 1 to 6 (both included)",
            params.arity
        ));
    }
    Ok(n_gates)
}

#[cfg(test)]
mod tests {
    use std::{marker::PhantomData, time::Instant};

    use anyhow::Result;
    use plonky2::hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    };

    use super::*;

    #[derive(Debug, Clone)]
    pub struct RecursiveTree<I: InnerCircuit> {
        _i: PhantomData<I>,
    }

    impl<I: InnerCircuit> RecursiveTree<I> {
        fn prepare_public_inputs(
            public_inputs: Vec<F>,
            verifier_data: VerifierCircuitData<F, C, D>,
        ) -> Vec<F> {
            RecursiveCircuit::<I>::prepare_public_inputs(public_inputs, verifier_data)
        }

        fn prove_node(
            prover: &ProverCircuitData<F, C, D>,
            circuit: &mut RecursiveCircuit<I>,
            dummy_proof: Proof,
            innercircuit_input: I::Input,
            recursive_proofs: Vec<Proof>,
            // this is for the sake of testing, not for real usage
            non_base_node: bool, // false=skip proof check, true=verify proof
        ) -> Result<Proof> {
            // fill the targets
            let mut pw = PartialWitness::new();
            circuit.set_targets(
                &mut pw,
                dummy_proof,
                innercircuit_input,
                recursive_proofs,
                non_base_node,
            )?;

            let new_proof = prover.prove(pw)?;

            Ok(new_proof.proof)
        }
    }

    pub struct InnerCircuitTargets {
        input_targ: HashOutTarget,
        _output_targ: HashOutTarget,
    }

    #[derive(Clone, Debug)]
    pub struct Circuit1 {}
    impl InnerCircuit for Circuit1 {
        type Targets = InnerCircuitTargets;
        type Input = HashOut<F>;
        fn build(
            builder: &mut CircuitBuilder<F, D>,
            _public_inputs: Vec<Target>,
            _selectors: Vec<BoolTarget>,
        ) -> Result<Self::Targets> {
            let input_targ = builder.add_virtual_hashes(1)[0];

            let mut output_targ: HashOutTarget = input_targ;
            for _ in 0..100 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            Ok(InnerCircuitTargets {
                input_targ,
                _output_targ: output_targ,
            })
        }

        fn set_targets(
            pw: &mut PartialWitness<F>,
            targets: &Self::Targets,
            input: &Self::Input,
        ) -> Result<Vec<F>> {
            pw.set_hash_target(targets.input_targ, *input)?;

            Ok(vec![])
        }
    }
    #[derive(Clone, Debug)]
    pub struct Circuit2 {}
    impl InnerCircuit for Circuit2 {
        type Targets = InnerCircuitTargets;
        type Input = HashOut<F>;
        fn build(
            builder: &mut CircuitBuilder<F, D>,
            _public_inputs: Vec<Target>,
            _selectors: Vec<BoolTarget>,
        ) -> Result<Self::Targets> {
            let input_targ = builder.add_virtual_hashes(1)[0];

            let mut output_targ: HashOutTarget = input_targ;
            for _ in 0..2000 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            Ok(InnerCircuitTargets {
                input_targ,
                _output_targ: output_targ,
            })
        }

        fn set_targets(
            pw: &mut PartialWitness<F>,
            targets: &Self::Targets,
            input: &Self::Input,
        ) -> Result<Vec<F>> {
            pw.set_hash_target(targets.input_targ, *input)?;

            Ok(vec![])
        }
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
        type RT<I> = RecursiveTree<I>;

        // build the circuit_data & verifier_data for the recursive circuit
        let start = Instant::now();
        let circuit_data = RC::<Circuit1>::circuit_data(&params)?;
        let verifier_data = circuit_data.verifier_data();
        let prover = RC::<Circuit1>::build_prover(&params, verifier_data.clone())?;

        let dummy_proof = RC::<Circuit1>::dummy_proof(circuit_data);
        println!("recursive params generated {:?}", start.elapsed());

        // build 1st circuit: circuit1, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit1
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config.clone());
        let start = Instant::now();
        let mut circuit = RC::<Circuit1>::build(&mut builder, &params, verifier_data.clone())?;
        println!("RecursiveCircuit::build(): {:?}", start.elapsed());
        println!("Circuit1 num_gates {}", builder.num_gates());

        // build 2nd circuit: circuit2, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit2
        let mut builder2 = CircuitBuilder::new(config);
        let mut circuit2 = RC::<Circuit2>::build(&mut builder2, &params, verifier_data.clone())?;
        println!("Circuit2 num_gates {}", builder2.num_gates());

        // we start with 0 proofs at the first iteration
        let mut proofs_at_level_i: Vec<Proof> = vec![];

        // loop over the recursion levels
        for i in 0..n_steps {
            let mut next_level_proofs: Vec<Proof> = vec![];

            // loop over the nodes of each recursion tree level
            for j in 0..arity {
                let innercircuit_input = HashOut::<F>::ZERO;

                let non_base_node: bool = i > 0; // set true/false

                // do the recursive step
                let start = Instant::now();
                let new_proof = RT::<Circuit1>::prove_node(
                    &prover,
                    &mut circuit,
                    dummy_proof.clone(),
                    innercircuit_input,
                    proofs_at_level_i.clone(),
                    non_base_node,
                )?;
                println!(
                    "RecursiveTree::prove_node (level: i={}, node: j={}) took: {:?}ms",
                    i,
                    j,
                    start.elapsed()
                );

                // verify the recursive proof
                let public_inputs =
                    RT::<Circuit1>::prepare_public_inputs(vec![], verifier_data.clone());
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
        let innercircuit_input = HashOut::<F>::ZERO;
        let new_proof = RT::<Circuit2>::prove_node(
            &prover,
            &mut circuit2,
            dummy_proof.clone(),
            innercircuit_input,
            proofs_at_level_i,
            true,
        )?;
        let public_inputs = RT::<Circuit2>::prepare_public_inputs(vec![], verifier_data.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data.clone().verify(ProofWithPublicInputs {
            proof: new_proof.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // do another final iteration, back with Circuit1
        let innercircuit_input = HashOut::<F>::ZERO;
        let new_proof = RT::<Circuit1>::prove_node(
            &prover,
            &mut circuit,
            dummy_proof,
            innercircuit_input,
            vec![new_proof],
            true,
        )?;
        let public_inputs = RT::<Circuit1>::prepare_public_inputs(vec![], verifier_data.clone());
        verifier_data.clone().verify(ProofWithPublicInputs {
            proof: new_proof.clone(),
            public_inputs: public_inputs.clone(),
        })?;
        proofs_at_level_i = vec![new_proof];

        assert_eq!(proofs_at_level_i.len(), 1);
        let last_proof = proofs_at_level_i[0].clone();

        // verify the last proof
        let public_inputs = RT::<Circuit1>::prepare_public_inputs(vec![], verifier_data.clone());
        let pis = ProofWithPublicInputs {
            proof: last_proof.clone(),
            public_inputs: public_inputs.clone(),
        };
        verifier_data.clone().verify(pis.clone())?;

        Ok(())
    }

    #[test]
    fn test_recursive_circuit() -> Result<()> {
        // arity=1, n_steps=4
        test_recursive_circuit_opt(1, 4)?;

        // arity=2, n_steps=3
        // test_recursive_circuit_opt(2, 3)?; // commented to be skipped in the CI since it's slower

        Ok(())
    }
}
