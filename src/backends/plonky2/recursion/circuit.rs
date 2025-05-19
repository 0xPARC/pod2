/// This file contains the RecursiveCircuit, the circuit used for recursion.
///
/// The RecursiveCircuit verifies N proofs (N=arity), together with the logic
/// defined at the InnerCircuit (in our case, used for the MainPodCircuit
/// logic).
///
/// The arity defines the maximum amount of proofs that the RecursiveCircuit
/// verifies. When arity>1, using the RecursiveCircuit has the shape of a tree
/// of the same arity.
///
use hashbrown::HashMap;
use plonky2::{
    self,
    gates::noop::NoopGate,
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
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
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    recursion::dummy_circuit::{dummy_circuit, dummy_proof as plonky2_dummy_proof},
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
    let circuit_data = RecursiveCircuit::<I>::circuit_data(arity, inner_params)?;
    let common_data = circuit_data.common.clone();
    let verifier_data = circuit_data.verifier_data();
    let dummy_proof = RecursiveCircuit::<I>::dummy_proof(circuit_data)?;
    Ok(RecursiveParams {
        arity,
        common_data,
        dummy_proof,
        dummy_verifier_data: verifier_data,
    })
}

/// RecursiveCircuit defines the circuit that verifies `arity` proofs.
pub struct RecursiveCircuit<I: InnerCircuit> {
    params: RecursiveParams,
    prover: ProverCircuitData<F, C, D>,
    targets: RecursiveCircuitTargets<I>,
}

#[derive(Clone, Debug)]
pub struct RecursiveCircuitTargets<I: InnerCircuit> {
    selectors_targ: Vec<BoolTarget>,
    innercircuit_targ: I,
    proofs_targ: Vec<ProofWithPublicInputsTarget<D>>,
    prev_verifier_datas_hashes: Vec<HashOutTarget>,
    vds_hash: HashOutTarget,
    verifier_datas_targ: Vec<VerifierCircuitTarget>,
}

impl<I: InnerCircuit> RecursiveCircuit<I> {
    pub fn prove(
        &mut self,
        inner_inputs: I::Input,
        proofs: Vec<Proof>,
        prev_hashes: Vec<HashOut<F>>,
        verifier_datas: Vec<VerifierCircuitData<F, C, D>>,
    ) -> Result<(Proof, HashOut<F>)> {
        let mut pw = PartialWitness::new();
        let vds_hash = self.set_targets(
            &mut pw,
            inner_inputs, // innercircuit_input
            proofs,
            prev_hashes,
            verifier_datas,
        )?;
        let proof = self.prover.prove(pw)?;
        Ok((proof.proof, vds_hash))
    }

    /// builds the targets and returns also a ProverCircuitData
    pub fn build(params: &RecursiveParams, inner_params: &I::Params) -> Result<Self> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config.clone());

        let targets: RecursiveCircuitTargets<I> =
            Self::build_targets(&mut builder, params, inner_params)?;

        println!("RecursiveCircuit<I> num_gates {}", builder.num_gates());

        let prover: ProverCircuitData<F, C, D> = builder.build_prover::<C>();
        Ok(Self {
            params: params.clone(),
            prover,
            targets,
        })
    }

    /// builds the targets
    pub fn build_targets(
        builder: &mut CircuitBuilder<F, D>,
        params: &RecursiveParams,
        inner_params: &I::Params,
    ) -> Result<RecursiveCircuitTargets<I>> {
        let selectors_targ: Vec<BoolTarget> = (0..params.arity)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();

        // TODO: investigate
        builder.add_gate(
            // add a ConstantGate, because without this, when later generating the `dummy_circuit`
            // (inside the `conditionally_verify_cyclic_proof_or_dummy`), it fails due the
            // `CommonCircuitData` of the generated circuit not matching the given `CommonCircuitData`
            // to create it. Without this it fails because it misses a ConstantGate.
            plonky2::gates::constant::ConstantGate::new(params.common_data.config.num_constants),
            vec![],
        );

        // proof verification
        let verifier_datas_targ: Vec<VerifierCircuitTarget> = (0..params.arity)
            .map(|_| builder.add_virtual_verifier_data(builder.config.fri_config.cap_height))
            .collect();
        let proofs_targ: Result<Vec<ProofWithPublicInputsTarget<D>>> = (0..params.arity)
            .map(|i| {
                let proof_targ = builder.add_virtual_proof_with_pis(&params.common_data);
                builder.conditionally_verify_proof_or_dummy::<C>(
                    selectors_targ[i],
                    &proof_targ,
                    &verifier_datas_targ[i],
                    &params.common_data,
                )?;
                Ok(proof_targ)
            })
            .collect();
        let proofs_targ = proofs_targ?;

        // hash the various verifier_data
        let prev_verifier_datas_hashes = builder.add_virtual_hashes(params.arity);
        let vds_hash = gadget_hash_verifier_datas(
            builder,
            params.arity,
            prev_verifier_datas_hashes.clone(),
            verifier_datas_targ.clone(),
        );
        // set vds_hash as public input
        builder.register_public_inputs(&vds_hash.elements);

        // get the targets of the public inputs used to verify the proofs in-circuit, to be used in
        // the InnerCircuit
        let internal_proof_pub_inp: Vec<Target> = proofs_targ
            .iter()
            .flat_map(|proof_pis| proof_pis.public_inputs.clone())
            .collect();

        // build the InnerCircuits logic
        let innercircuit_targ: I = I::build(
            builder,
            inner_params,
            internal_proof_pub_inp,
            selectors_targ.clone(),
        )?;

        Ok(RecursiveCircuitTargets {
            selectors_targ,
            innercircuit_targ,
            proofs_targ,
            prev_verifier_datas_hashes,
            vds_hash,
            verifier_datas_targ,
        })
    }

    pub fn set_targets(
        &mut self,
        pw: &mut PartialWitness<F>,
        innercircuit_input: I::Input,
        recursive_proofs: Vec<Proof>,
        prev_verifier_datas_hashes: Vec<HashOut<F>>,
        verifier_datas: Vec<VerifierCircuitData<F, C, D>>,
    ) -> Result<HashOut<F>> {
        let n = recursive_proofs.len();
        assert!(n <= self.params.arity);
        assert_eq!(n, verifier_datas.len());

        // fill the missing proofs with dummy_proofs
        let dummy_proofs: Vec<Proof> = (n..self.params.arity)
            .map(|_| self.params.dummy_proof.clone())
            .collect();
        let recursive_proofs: Vec<Proof> = [recursive_proofs, dummy_proofs].concat();

        // fill the missing prev_verifier_data_hashes with the 'zero' hash
        let mut prev_verifier_datas_hashes = prev_verifier_datas_hashes.clone();
        prev_verifier_datas_hashes.resize(self.params.arity, HashOut::<F>::ZERO);

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
                &self.targets.verifier_datas_targ[i],
                &verifier_datas[i].verifier_only,
            )?;

            // put together the public inputs with the verifier_data. Note:
            // current version doesn't use InnerCircuit's public inputs (vec![])
            let proof_i_public_inputs =
                Self::prepare_public_inputs(vec![], prev_verifier_datas_hashes[i]);

            pw.set_proof_with_pis_target(
                &self.targets.proofs_targ[i],
                &ProofWithPublicInputs {
                    proof: recursive_proofs[i].clone(),
                    public_inputs: proof_i_public_inputs.clone(),
                },
            )?;
        }

        #[allow(clippy::needless_range_loop)]
        for i in 0..self.params.arity {
            pw.set_hash_target(
                self.targets.prev_verifier_datas_hashes[i],
                prev_verifier_datas_hashes[i],
            )?;
        }

        // vds_hash is returned since it will be used as public input to verify
        // the proof of the current instance of the circuit
        let vds_hash = hash_verifier_datas(
            self.params.arity,
            prev_verifier_datas_hashes.clone(),
            verifier_datas.clone(),
        );
        pw.set_hash_target(self.targets.vds_hash, vds_hash)?;

        Ok(vds_hash)
    }

    /// returns the full-recursive CircuitData
    pub fn circuit_data(arity: usize, inner_params: &I::Params) -> Result<CircuitData<F, C, D>> {
        let data: CircuitData<F, C, D> = common_data_for_recursion::<I>(arity, inner_params)?;
        let common_data = data.common.clone();
        let verifier_data = data.verifier_data();
        let dummy_proof = Self::dummy_proof(data)?;
        let params = RecursiveParams {
            arity,
            common_data,
            dummy_proof,
            dummy_verifier_data: verifier_data,
        };

        // build the actual RecursiveCircuit circuit data
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::new(config);

        let _ = Self::build_targets(&mut builder, &params, inner_params)?;
        let data = builder.build::<C>();

        Ok(data)
    }

    pub fn dummy_proof(circuit_data: CircuitData<F, C, D>) -> Result<Proof> {
        let dummy_circuit_data = dummy_circuit(&circuit_data.common);
        let dummy_proof_pis = plonky2_dummy_proof(&dummy_circuit_data, HashMap::new())?;
        Ok(dummy_proof_pis.proof)
    }

    pub fn prepare_public_inputs(
        public_inputs: Vec<F>,
        prev_verifier_datas_hash: HashOut<F>,
    ) -> Vec<F> {
        [public_inputs, prev_verifier_datas_hash.elements.to_vec()].concat()
    }
}

fn hash_verifier_datas(
    arity: usize,
    prev_hashes: Vec<HashOut<F>>,
    verifier_datas: Vec<VerifierCircuitData<F, C, D>>,
) -> HashOut<F> {
    // sanity check
    assert_eq!(verifier_datas.len(), arity);

    let zero_hash = HashOut::<F>::ZERO;
    let mut prev_hashes = prev_hashes.clone();
    prev_hashes.resize(arity, zero_hash);
    let prev_hashes: Vec<F> = prev_hashes
        .iter()
        .flat_map(|h| h.elements.to_vec())
        .collect();

    let hashes: Vec<F> = verifier_datas
        .iter()
        .flat_map(|vd| hash_verifier_data(vd).elements)
        .collect();

    let inp: Vec<F> = [prev_hashes, hashes].concat();

    PoseidonHash::hash_no_pad(&inp)
}
fn hash_verifier_data(verifier_data: &VerifierCircuitData<F, C, D>) -> HashOut<F> {
    let f: Vec<F> = [
        verifier_data.verifier_only.circuit_digest.elements.to_vec(),
        verifier_data
            .verifier_only
            .constants_sigmas_cap
            .0
            .iter()
            .flat_map(|e| e.elements)
            .collect(),
    ]
    .concat();
    PoseidonHash::hash_no_pad(&f)
}

fn gadget_hash_verifier_datas(
    builder: &mut CircuitBuilder<F, D>,
    arity: usize,
    prev_hashes: Vec<HashOutTarget>,
    verifier_datas: Vec<VerifierCircuitTarget>,
) -> HashOutTarget {
    // sanity checks
    assert_eq!(prev_hashes.len(), arity);
    assert_eq!(verifier_datas.len(), arity);

    let prev_hashes: Vec<Target> = prev_hashes
        .iter()
        .flat_map(|h| h.elements.to_vec())
        .collect();

    let hashes: Vec<Target> = verifier_datas
        .iter()
        .flat_map(|vd| gadget_hash_verifier_data(builder, vd).elements)
        .collect();

    let inp: Vec<Target> = [prev_hashes, hashes].concat();

    builder.hash_n_to_hash_no_pad::<PoseidonHash>(inp)
}
fn gadget_hash_verifier_data(
    builder: &mut CircuitBuilder<F, D>,
    verifier_data: &VerifierCircuitTarget,
) -> HashOutTarget {
    let f: Vec<Target> = [
        verifier_data.circuit_digest.elements.to_vec(),
        verifier_data
            .constants_sigmas_cap
            .0
            .iter()
            .flat_map(|e| e.elements)
            .collect(),
    ]
    .concat();
    builder.hash_n_to_hash_no_pad::<PoseidonHash>(f)
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
    for _ in 0..arity {
        let verifier_data_i =
            builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);

        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, &verifier_data_i, &data.common);
    }
    let data = builder.build::<C>();

    // 3rd
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    builder.add_gate(
        plonky2::gates::constant::ConstantGate::new(config.num_constants),
        vec![],
    );

    let verifier_datas_targ: Vec<VerifierCircuitTarget> = (0..arity)
        .map(|_| builder.add_virtual_verifier_data(builder.config.fri_config.cap_height))
        .collect();
    for vd_i in verifier_datas_targ.iter() {
        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, vd_i, &data.common);
    }

    let prev_verifier_datas_hashes = builder.add_virtual_hashes(arity);
    let vds_hash = gadget_hash_verifier_datas(
        &mut builder,
        arity,
        prev_verifier_datas_hashes.clone(),
        verifier_datas_targ.clone(),
    );
    // set vds_hash as public input
    builder.register_public_inputs(&vds_hash.elements);

    // set the targets for the InnerCircuit
    let _ = I::build(&mut builder, inner_params, vec![], vec![])?;

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
        for _ in 0..100 {
            out = PoseidonHash::hash_no_pad(&out.elements)
        }
        out
    }
    // out-of-circuit input-output computation for Circuit2
    // fn circuit2_io(inp: HashOut<F>) -> HashOut<F> {
    //     let mut out: HashOut<F> = inp;
    //     for _ in 0..2000 {
    //         out = PoseidonHash::hash_no_pad(&out.elements)
    //     }
    //     out
    // }
    // out-of-circuit input-output computation for Circuit2
    fn circuit2_io(inp: HashOut<F>) -> HashOut<F> {
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

    #[test]
    fn test_hash_verifier_datas() -> Result<()> {
        let arity: usize = 2;
        let circuit_data = RecursiveCircuit::<Circuit1>::circuit_data(1, &())?;
        let verifier_data = circuit_data.verifier_data();

        let h = hash_verifier_datas(
            arity,
            vec![],
            vec![verifier_data.clone(), verifier_data.clone()],
        );

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        // circuit logic
        let vd_targ1 = builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);
        let vd_targ2 = builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);
        let expected_h = builder.add_virtual_hash();
        let prev_hashes_targ = builder.add_virtual_hashes(arity);

        let h_targ = gadget_hash_verifier_datas(
            &mut builder,
            arity,
            prev_hashes_targ.clone(),
            vec![vd_targ1.clone(), vd_targ2.clone()],
        );
        builder.connect_hashes(expected_h, h_targ);

        // set targets
        for ph_targ in prev_hashes_targ {
            pw.set_hash_target(ph_targ, HashOut::<F>::ZERO)?;
        }
        pw.set_hash_target(expected_h, h)?;
        pw.set_verifier_data_target(&vd_targ1, &verifier_data.verifier_only)?;
        pw.set_verifier_data_target(&vd_targ2, &verifier_data.verifier_only)?;
        pw.set_hash_target(expected_h, h)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    #[test]
    fn test_recursive_circuit() -> Result<()> {
        let arity: usize = 2;

        type RC<I> = RecursiveCircuit<I>;
        let inner_params = ();
        let params: RecursiveParams = new_params::<Circuit1>(arity, &inner_params)?;

        // build the circuit_data & verifier_data for the recursive circuit
        let start = Instant::now();
        let circuit_data_1 = RC::<Circuit1>::circuit_data(arity, &inner_params)?;
        let verifier_data_1 = circuit_data_1.verifier_data();

        let circuit_data_2 = RC::<Circuit2>::circuit_data(arity, &inner_params)?;
        let verifier_data_2 = circuit_data_2.verifier_data();

        println!(
            "new_params & (c1, c2).circuit_data generated {:?}",
            start.elapsed()
        );

        let mut circuit1 = RC::<Circuit1>::build(&params, &())?;
        let mut circuit2 = RC::<Circuit2>::build(&params, &())?;

        dbg!("circuit1.prove");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let (proof_1a, vds_hash_1a) = circuit1.prove(inner_inputs, vec![], vec![], vec![])?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(
            vec![], // inner_circuit public_inputs
            vds_hash_1a,
        );
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1a.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        dbg!("circuit1.prove (2nd iteration), verifies the proof of 1st iteration with circuit1");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let (proof_1b, vds_hash_1b) = circuit1.prove(
            inner_inputs,
            vec![proof_1a.clone()],
            vec![vds_hash_1a],
            vec![verifier_data_1.clone()],
        )?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(vec![], vds_hash_1b);
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1b.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // generate a proof of Circuit2, which internally verifies the proof_1b
        dbg!("circuit2.prove, which internally verifies the proof_1b");
        let inner_inputs = (inp, circuit2_io(inp));
        let (proof_2, vds_hash_2) = circuit2.prove(
            inner_inputs,
            vec![proof_1b.clone()],
            vec![vds_hash_1b],
            vec![verifier_data_1.clone()],
        )?;
        let public_inputs = RC::<Circuit2>::prepare_public_inputs(vec![], vds_hash_2);
        verifier_data_2.clone().verify(ProofWithPublicInputs {
            proof: proof_2.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        // verify the last proof of circuit2, inside a new circuit1's proof
        dbg!("proof_1c = c1.prove([proof_1b, proof_2], [verifier_data_1, verifier_data_2])");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let (proof_1c, vds_hash_1c) = circuit1.prove(
            inner_inputs,
            vec![proof_1b, proof_2],
            vec![vds_hash_1b, vds_hash_2],
            vec![verifier_data_1.clone(), verifier_data_2.clone()],
        )?;
        let public_inputs = RC::<Circuit1>::prepare_public_inputs(vec![], vds_hash_1c);
        verifier_data_1.clone().verify(ProofWithPublicInputs {
            proof: proof_1c.clone(),
            public_inputs: public_inputs.clone(),
        })?;

        Ok(())
    }
}
