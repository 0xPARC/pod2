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
            CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData, VerifierCircuitData,
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
    common_data: CommonCircuitData<F, D>,
    dummy_proof: Proof,
    dummy_verifier_data: VerifierCircuitData<F, C, D>,
}

pub fn new_params<I: InnerCircuit>(
    arity: usize,
    inner_params: &I::Params,
) -> Result<RecursiveParams> {
    let circuit_data = RecursiveCircuit::<I>::circuit_data(arity, &inner_params)?;
    let common_data = circuit_data.common.clone();
    let verifier_data = circuit_data.verifier_data();
    let dummy_proof = RecursiveCircuit::<I>::dummy_proof(circuit_data);
    Ok(RecursiveParams {
        arity,
        common_data,
        dummy_proof,
        dummy_verifier_data: verifier_data,
    })
}

/// RecursiveCircuit defines the circuit that verifies `arity` proofs of itself.
pub struct RecursiveCircuit<I: InnerCircuit> {
    params: RecursiveParams,
    prover: ProverCircuitData<F, C, D>,
    targets: RecursiveCircuitTargets<I>,
    // verifier_data: VerifierCircuitData<F, C, D>,
}
#[derive(Clone, Debug)]
pub struct RecursiveCircuitTargets<I: InnerCircuit> {
    selectors_targ: Vec<BoolTarget>,
    innercircuit_targ: I,
    proofs_targ: Vec<ProofWithPublicInputsTarget<D>>,
    // cyclic-recursion params:
    verifier_data_targ: Vec<VerifierCircuitTarget>,
}

impl<I: InnerCircuit> RecursiveCircuit<I> {
    pub fn prove(
        &mut self,
        inner_inputs: I::Input,
        proofs: Vec<Proof>,
        verifier_datas: Vec<VerifierCircuitData<F, C, D>>,
    ) -> Result<Proof> {
        let mut pw = PartialWitness::new();
        self.set_targets(
            &mut pw,
            inner_inputs, // innercircuit_input
            proofs.clone(),
            verifier_datas,
        )?;
        let proof = self.prover.prove(pw)?.proof;
        Ok(proof)
    }

    pub fn build(
        params: &RecursiveParams,
        inner_params: &I::Params,
        // self's verifier_data
        // verifier_data: VerifierCircuitData<F, C, D>, // TODO rm
        // common_data: CommonCircuitData<F, D>, // TODO wip. TODO move to a RecursiveCircuitBuilder
    ) -> Result<Self> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config.clone());

        let targets: RecursiveCircuitTargets<I> =
            Self::build_opt(&mut builder, params, inner_params)?;

        println!("RecursiveCircuit<I> num_gates {}", builder.num_gates());

        let prover: ProverCircuitData<F, C, D> = builder.build_prover::<C>();
        Ok(Self {
            params: params.clone(),
            prover,
            targets,
        })
    }

    pub fn build_opt(
        builder: &mut CircuitBuilder<F, D>,
        params: &RecursiveParams,
        inner_params: &I::Params,
        // self's verifier_data
        // verifier_data: VerifierCircuitData<F, C, D>, // TODO rm
        // common_data: CommonCircuitData<F, D>, // TODO wip. TODO move to a RecursiveCircuitBuilder
    ) -> Result<RecursiveCircuitTargets<I>> {
        let selectors_targ: Vec<BoolTarget> = (0..params.arity)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();

        // proof verification
        let verifier_data_targ: Vec<VerifierCircuitTarget> = (0..params.arity)
            .map(|_| builder.add_verifier_data_public_inputs())
            .collect();
        let proofs_targ: Result<Vec<ProofWithPublicInputsTarget<D>>> = (0..params.arity)
            .map(|i| {
                let proof_targ = builder.add_virtual_proof_with_pis(&params.common_data);
                builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
                    selectors_targ[i],
                    &proof_targ,
                    &params.common_data,
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

        Ok(RecursiveCircuitTargets {
            selectors_targ,
            innercircuit_targ,
            proofs_targ,
            verifier_data_targ,
        })
    }

    pub fn set_targets(
        &mut self,
        pw: &mut PartialWitness<F>,
        innercircuit_input: I::Input,
        recursive_proofs: Vec<Proof>,
        verifier_datas: Vec<VerifierCircuitData<F, C, D>>,
    ) -> Result<()> {
        let n = recursive_proofs.len();
        assert!(n <= self.params.arity);
        // assert_eq!(recursive_proofs.len(), verifier_datas.len()); // TODO WIP

        // fill the missing proofs with dummy_proofs
        let dummy_proofs: Vec<Proof> = (n..self.params.arity)
            .map(|_| self.params.dummy_proof.clone())
            .collect();
        let recursive_proofs: Vec<Proof> = [recursive_proofs, dummy_proofs].concat();

        // fill the missing verifier_datas with dummy_verifier_datas
        let dummy_verifier_datas: Vec<VerifierCircuitData<F, C, D>> = (n..self.params.arity)
            .map(|_| self.params.dummy_verifier_data.clone())
            .collect();
        let verifier_datas: Vec<VerifierCircuitData<F, C, D>> =
            [verifier_datas, dummy_verifier_datas].concat();

        // set the first n selectors to true, and the rest to false
        for i in 0..n {
            pw.set_bool_target(self.targets.selectors_targ[i], true)?;
        }
        for i in n..self.params.arity {
            pw.set_bool_target(self.targets.selectors_targ[i], false)?;
        }

        // set the InnerCircuit related values
        self.targets
            .innercircuit_targ
            .set_targets(pw, &innercircuit_input)?;

        #[allow(clippy::needless_range_loop)]
        for i in 0..self.params.arity {
            pw.set_verifier_data_target(
                &self.targets.verifier_data_targ[i],
                &verifier_datas[i].verifier_only,
            )?; // TODO WIP

            // put together the public inputs with the verifier_data. Note:
            // current version doesn't use InnerCircuit's public inputs (vec![])
            let public_inputs = Self::prepare_public_inputs(vec![], verifier_datas[0].clone());

            pw.set_proof_with_pis_target(
                &self.targets.proofs_targ[i],
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
        // params: &RecursiveParams,
        arity: usize,
        inner_params: &I::Params,
    ) -> Result<CircuitData<F, C, D>> {
        let data: CircuitData<F, C, D> = common_data_for_recursion::<I>(arity, inner_params)?;
        let common_data = data.common.clone();
        let verifier_data = data.verifier_data();
        let dummy_proof = Self::dummy_proof(data);
        let params = RecursiveParams {
            arity,
            common_data,
            dummy_proof,
            dummy_verifier_data: verifier_data,
        };

        // build the actual RecursiveCircuit circuit data
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build_opt(&mut builder, &params, inner_params)?;
        let data = builder.build::<C>();

        Ok(data)
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
    arity: usize,
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
    for _ in 0..arity {
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
    for _ in 0..arity {
        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    }

    // pad min gates
    let n_gates = compute_num_gates(arity)?;
    while builder.num_gates() < n_gates {
        builder.add_gate(NoopGate, vec![]);
    }
    Ok(builder.build::<C>())
}

fn compute_num_gates(arity: usize) -> Result<usize> {
    // Note: the following numbers are WIP, obtained by trial-error by running different
    // configurations in the tests.
    let n_gates = match arity {
        0..=1 => 1 << 12,
        2 => 1 << 13,
        3..=5 => 1 << 14,
        6 => 1 << 15,
        _ => 0,
    };
    if n_gates == 0 {
        return Err(Error::custom(format!(
            "arity={} not supported. Currently supported arity from 1 to 6 (both included)",
            arity
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
        for _ in 0..2000 {
            out = PoseidonHash::hash_no_pad(&out.elements)
        }
        out
    }
    // out-of-circuit input-output computation for Circuit2
    fn circuit2_io(inp: HashOut<F>) -> HashOut<F> {
        let mut out: HashOut<F> = inp;
        for _ in 0..100 {
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

    /*
    - c1 = RecursiveCircuit<Circuit1>
    - c2 = Circuit2
    // c1 & c2

    - proof_1a = c1.prove([null, null], [null, null])
    - proof_1b = c1.prove([proof_1a, null], [verifier_data_c1, null])
    - proof_2 = c2.prove(c2_inputs)

    - proof_1c = c1.prove([proof_1b, proof_2], [verifier_data_c1, verifier_data_c2])


    */

    fn test_recursive_circuit_opt(
        // arity: number of cyclic recursion proofs verified at each node of the
        // recursion tree
        arity: usize,
        // n_steps: determines the number of recursive steps. Notice that when
        // arity>1, n_steps determines the number of levels of the recursive
        // tree
        n_steps: usize,
    ) -> Result<()> {
        type RC<I> = RecursiveCircuit<I>;
        let inner_params = ();

        let params: RecursiveParams = new_params::<Circuit1>(arity, &inner_params)?;

        // build the circuit_data & verifier_data for the recursive circuit
        let start = Instant::now();
        let circuit_data_1 = RC::<Circuit1>::circuit_data(arity, &inner_params)?;
        let verifier_data_1 = circuit_data_1.verifier_data();

        let circuit_data_2 = RC::<Circuit2>::circuit_data(arity, &inner_params)?;
        let verifier_data_2 = circuit_data_2.verifier_data();

        // let circuit_data_3 = RC::<Circuit3>::circuit_data(arity, &inner_params)?;
        // let verifier_data_3 = circuit_data_3.verifier_data();

        // let dummy_proof = RC::<Circuit1>::dummy_proof(circuit_data_1);
        println!(
            "circuit_data,prover,dummy_proof generated {:?}",
            start.elapsed()
        );

        // build 1st circuit: circuit1, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit1
        let mut circuit1 = RC::<Circuit1>::build(&params, &())?;

        // build 2nd circuit: circuit2, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit2
        let mut circuit2 = RC::<Circuit2>::build(&params, &())?;

        // build 3rd circuit: circuit3, a RecursiveCircuit which uses as
        // InnerCircuit the Circuit3
        // let circuit3 = RC::<Circuit3>::build(&params, &())?;

        // TODO use circuit4 in the test
        // circuit4 is the Circuit3 without the RecursiveCircuit wrapper
        // let mut builder4 = CircuitBuilder::new(config);
        // let mut circuit4 = Circuit3::build(&mut builder4, &(), vec![], vec![])?;
        // println!("Circuit4 num_gates {}", builder4.num_gates());

        // we start with 0 proofs at the first iteration, which means that
        // internally at RecursiveCircuit.set_targets, it will use all
        // dummy_proofs

        dbg!("circuit1.prove");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1a =
            // circuit1.prove(inner_inputs, vec![], vec![verifier_data_1.clone()])?;
            circuit1.prove(inner_inputs, vec![], vec![])?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(vec![], verifier_data_1.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1a.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        dbg!("circuit1.prove (2nd iteration), verifies the proof of 1st iteration with circuit1");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1b = circuit1.prove(
            inner_inputs,
            vec![proof_1a.clone()],
            vec![verifier_data_1.clone()],
        )?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(vec![], verifier_data_1.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1b.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // do one more iteration, but now with Circuit2
        dbg!("circuit2.prove");
        let inner_inputs = (inp, circuit2_io(inp));
        let proof_2 = circuit2.prove(inner_inputs, vec![], vec![verifier_data_2.clone()])?;
        let public_inputs = RC::<Circuit2>::prepare_public_inputs(vec![], verifier_data_2.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data_2.clone().verify(ProofWithPublicInputs {
            proof: proof_2.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        dbg!("proof_1c = c1.prove([proof_1b, proof_2], [verifier_data_c1, verifier_data_c2])");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1c =
            circuit1.prove(inner_inputs, vec![proof_2], vec![verifier_data_2.clone()])?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(vec![], verifier_data_2.clone());
        // Notice that this is the `verifier_data` of Circuit1:
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1c.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // do another final iteration, now with Circuit3
        // dbg!("circuit3.prove");
        // let inner_inputs = (inp, circuit3_io(inp));
        // let proof3 = circuit3.prove(inner_inputs, initial_proofs, vec![verifier_data_3.clone()])?;
        // let public_inputs = RC::<Circuit3>::prepare_public_inputs(vec![], verifier_data_3.clone());
        // verifier_data_3.clone().verify(ProofWithPublicInputs {
        //     proof: proof3.clone(),
        //     public_inputs: public_inputs.clone(),
        // })?;
        //
        // // verify the last proof
        // let public_inputs = RC::<Circuit3>::prepare_public_inputs(vec![], verifier_data_3.clone());
        // let pis = ProofWithPublicInputs {
        //     proof: proof3.clone(),
        //     public_inputs: public_inputs.clone(),
        // };
        // verifier_data_3.clone().verify(pis.clone())?;

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
