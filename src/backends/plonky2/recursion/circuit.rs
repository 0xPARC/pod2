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
use itertools::Itertools;
use plonky2::{
    self,
    field::{extension::quintic::QuinticExtension, types::Field},
    gates::{gate::GateRef, noop::NoopGate},
    hash::{
        hash_types::{HashOut, HashOutTarget},
        poseidon::PoseidonHash,
    },
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData, VerifierCircuitData,
            VerifierCircuitTarget, VerifierOnlyCircuitData,
        },
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    util::log2_ceil,
};
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        error::Result,
        primitives::ec::gates::{
            curve::ECAddHomogOffset, field::NNFMulSimple, generic::GateAdapter,
        },
    },
    measure_gates_begin, measure_gates_end,
    middleware::F,
    timed,
};

#[derive(Clone, Debug)]
pub struct VerifiedProofTarget {
    pub public_inputs: Vec<Target>,
    pub verifier_data_hash: HashOutTarget,
}

/// Expected maximum number of constant gates
const MAX_CONSTANT_GATES: usize = 64;

impl VerifiedProofTarget {
    fn add_virtual(builder: &mut CircuitBuilder<F, D>, num_public_inputs: usize) -> Self {
        Self {
            public_inputs: (0..num_public_inputs)
                .map(|_| builder.add_virtual_target())
                .collect_vec(),
            verifier_data_hash: builder.add_virtual_hash(),
        }
    }
}

/// InnerCircuit is the trait used to define the logic of the circuit that is
/// computed inside the RecursiveCircuit.
pub trait InnerCircuit: Sized {
    type Input; // Input for witness generation
    type Params; // Configuration parameters

    fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &Self::Params,
        verified_proofs: &[VerifiedProofTarget],
    ) -> Result<Self>;

    /// assigns the values to the targets
    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &Self::Input) -> Result<()>;
}

#[derive(Clone, Debug)]
pub struct RecursiveParams {
    /// determines the arity of the RecursiveCircuit
    pub(crate) arity: usize,
    pub(crate) common_data: CommonCircuitData<F, D>,
    pub(crate) verifier_data: VerifierCircuitData<F, C, D>,
}

impl RecursiveParams {
    pub fn common_data(&self) -> &CommonCircuitData<F, D> {
        &self.common_data
    }
    pub fn verifier_data(&self) -> &VerifierCircuitData<F, C, D> {
        &self.verifier_data
    }
}

pub fn new_params<I: InnerCircuit>(
    arity: usize,
    num_public_inputs: usize,
    inner_params: &I::Params,
) -> Result<RecursiveParams> {
    let (_, circuit_data) =
        RecursiveCircuit::<I>::target_and_circuit_data(arity, num_public_inputs, inner_params)?;
    let common_data = circuit_data.common.clone();
    let verifier_data = circuit_data.verifier_data();
    Ok(RecursiveParams {
        arity,
        common_data,
        verifier_data,
    })
}

pub fn new_params_padded<I: InnerCircuit>(
    arity: usize,
    common_data: &CommonCircuitData<F, D>,
    inner_params: &I::Params,
) -> Result<RecursiveParams> {
    let (_, circuit_data) =
        RecursiveCircuit::<I>::target_and_circuit_data_padded(arity, common_data, inner_params)?;
    let common_data = circuit_data.common.clone();
    let verifier_data = circuit_data.verifier_data();
    Ok(RecursiveParams {
        arity,
        common_data,
        verifier_data,
    })
}

/// RecursiveCircuit defines the circuit that verifies `arity` proofs.
pub struct RecursiveCircuit<I: InnerCircuit> {
    pub(crate) params: RecursiveParams,
    pub(crate) prover: ProverCircuitData<F, C, D>,
    pub(crate) target: RecursiveCircuitTarget<I>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RecursiveCircuitTarget<I: InnerCircuit> {
    innercircuit_targ: I,
    proofs_targ: Vec<ProofWithPublicInputsTarget<D>>,
    verifier_datas_targ: Vec<VerifierCircuitTarget>,
}

impl<I: InnerCircuit> RecursiveCircuit<I> {
    pub fn prove(
        &self,
        inner_inputs: &I::Input,
        proofs: Vec<ProofWithPublicInputs<F, C, D>>,
        verifier_datas: Vec<VerifierOnlyCircuitData<C, D>>,
    ) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        self.set_targets(
            &mut pw,
            inner_inputs, // innercircuit_input
            proofs,
            verifier_datas,
        )?;
        Ok(self.prover.prove(pw)?)
    }

    /// builds the targets and returns also a ProverCircuitData
    pub fn build(params: &RecursiveParams, inner_params: &I::Params) -> Result<Self> {
        #[cfg(not(feature = "zk"))]
        let config = CircuitConfig::standard_recursion_config();
        #[cfg(feature = "zk")]
        let config = CircuitConfig::standard_recursion_zk_config();

        let mut builder = CircuitBuilder::new(config);

        let targets: RecursiveCircuitTarget<I> = Self::build_targets(
            &mut builder,
            params.arity,
            &params.common_data,
            inner_params,
        )?;

        println!("RecursiveCircuit<I> num_gates {}", builder.num_gates());

        let prover: ProverCircuitData<F, C, D> = builder.build_prover::<C>();
        Ok(Self {
            params: params.clone(),
            prover,
            target: targets,
        })
    }

    /// builds the targets and pad to match the input `common_data`
    pub fn build_targets(
        builder: &mut CircuitBuilder<F, D>,
        arity: usize,
        common_data: &CommonCircuitData<F, D>,
        inner_params: &I::Params,
    ) -> Result<RecursiveCircuitTarget<I>> {
        let measure = measure_gates_begin!(builder, "RecCircuit");
        // proof verification
        let verifier_datas_targ: Vec<VerifierCircuitTarget> = (0..arity)
            .map(|_| builder.add_virtual_verifier_data(builder.config.fri_config.cap_height))
            .collect();
        let proofs_targ: Vec<ProofWithPublicInputsTarget<D>> = (0..arity)
            .map(|i| {
                let measure_verify = measure_gates_begin!(builder, "VerifyProof");
                let proof_targ = builder.add_virtual_proof_with_pis(common_data);
                builder.verify_proof::<C>(&proof_targ, &verifier_datas_targ[i], common_data);
                measure_gates_end!(builder, measure_verify);
                proof_targ
            })
            .collect();

        let verified_proofs = (0..arity)
            .map(|i| VerifiedProofTarget {
                public_inputs: proofs_targ[i].public_inputs.clone(),
                // note: here we're hashing the verifier_data as Hash(vd.circuit_digest,
                // vd.constant_sigmas_cap), despite the circuit_digest is already a hash containing
                // the constant_sigmas_cap. Conceptually we would use the circuit_digest as the hash
                // of the verifier_data, but unfortunately, the recursion verification circuit does
                // not ensure this link.  Alternatively we could calculate an modified
                // circuit_digest, hashing as in the original plonky2's circuit_digest but
                // additionally checking it in-circuit. But since in terms of circuit costs would
                // require a hash (with similar amount of elements), the approach that we do is take
                // the already computed circuit_digest and hash it together with the
                // constant_sigmas_cap, doing the same computation in-circuit, obtaining a new hash
                // that we use to represent the verifier_data.
                verifier_data_hash: hash_verifier_data_gadget(builder, &verifier_datas_targ[i]),
            })
            .collect_vec();

        // Build the InnerCircuit logic
        let innercircuit_targ: I = I::build(builder, inner_params, &verified_proofs)?;

        measure_gates_end!(builder, measure);

        pad_circuit(builder, common_data);

        Ok(RecursiveCircuitTarget {
            innercircuit_targ,
            proofs_targ,
            verifier_datas_targ,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        innercircuit_input: &I::Input,
        recursive_proofs: Vec<ProofWithPublicInputs<F, C, D>>,
        verifier_datas: Vec<VerifierOnlyCircuitData<C, D>>,
    ) -> Result<()> {
        let n = recursive_proofs.len();
        assert_eq!(n, self.params.arity);
        assert_eq!(n, verifier_datas.len());

        // set the InnerCircuit related values
        self.target
            .innercircuit_targ
            .set_targets(pw, innercircuit_input)?;

        #[allow(clippy::needless_range_loop)]
        for i in 0..self.params.arity {
            pw.set_verifier_data_target(&self.target.verifier_datas_targ[i], &verifier_datas[i])?;
            pw.set_proof_with_pis_target(&self.target.proofs_targ[i], &recursive_proofs[i])?;
        }

        Ok(())
    }

    /// returns the target full-recursive circuit and its CircuitData
    pub fn target_and_circuit_data(
        arity: usize,
        num_public_inputs: usize,
        inner_params: &I::Params,
    ) -> Result<(RecursiveCircuitTarget<I>, CircuitData<F, C, D>)> {
        let rec_common_data = timed!(
            "common_data_for_recursion",
            common_data_for_recursion::<I>(arity, num_public_inputs, inner_params)?
        );

        // build the actual RecursiveCircuit circuit data
        #[cfg(not(feature = "zk"))]
        let config = CircuitConfig::standard_recursion_config();
        #[cfg(feature = "zk")]
        let config = CircuitConfig::standard_recursion_zk_config();

        let mut builder = CircuitBuilder::new(config);

        let target = timed!(
            "RecursiveCircuit<I>::build_targets",
            Self::build_targets(&mut builder, arity, &rec_common_data, inner_params)?
        );
        let data = timed!("RecursiveCircuit<I> build", builder.build::<C>());
        assert_eq!(rec_common_data, data.common);

        Ok((target, data))
    }

    /// returns the full-recursive CircuitData padded to share the input `common_data`
    pub fn target_and_circuit_data_padded(
        arity: usize,
        common_data: &CommonCircuitData<F, D>,
        inner_params: &I::Params,
    ) -> Result<(RecursiveCircuitTarget<I>, CircuitData<F, C, D>)> {
        // build the actual RecursiveCircuit circuit data
        #[cfg(not(feature = "zk"))]
        let config = CircuitConfig::standard_recursion_config();
        #[cfg(feature = "zk")]
        let config = CircuitConfig::standard_recursion_zk_config();

        let mut builder = CircuitBuilder::new(config);

        let target = timed!(
            "RecursiveCircuit<I>::build_targets",
            Self::build_targets(&mut builder, arity, common_data, inner_params)?
        );
        let data = timed!("RecursiveCircuit<I> build", builder.build::<C>());
        assert_eq!(*common_data, data.common);

        Ok((target, data))
    }
}

fn coset_interpolation_gate(
    subgroup_bits: usize,
    degree: usize,
    barycentric_weights: &[u64],
) -> plonky2::gates::coset_interpolation::CosetInterpolationGate<F, D> {
    #[allow(dead_code)]
    struct Mirror {
        subgroup_bits: usize,
        degree: usize,
        barycentric_weights: Vec<F>,
    }
    let barycentric_weights = barycentric_weights
        .iter()
        .map(|v| F::from_canonical_u64(*v))
        .collect_vec();
    let gate = Mirror {
        subgroup_bits,
        degree,
        barycentric_weights,
    };
    unsafe { std::mem::transmute(gate) }
}

/// Returns the minimum set of gates that define our recursively verifiable circuits.
/// NOTE: The overhead between verifying any proof with just the `NoopGate` and verifying a proof
/// with all these standard gates is about 400 num_gates (rows), no matter the circuit size.
fn standard_gates(config: &CircuitConfig) -> Vec<GateRef<F, D>> {
    let nnf_mul_simple =
        GateAdapter::<NNFMulSimple<5, QuinticExtension<F>>>::new_from_config(config);
    let ec_add_homog_offset = GateAdapter::<ECAddHomogOffset>::new_from_config(config);
    vec![
        GateRef::new(plonky2::gates::noop::NoopGate {}),
        GateRef::new(plonky2::gates::constant::ConstantGate::new(
            config.num_constants,
        )),
        GateRef::new(plonky2::gates::poseidon_mds::PoseidonMdsGate::new()),
        GateRef::new(plonky2::gates::poseidon::PoseidonGate::new()),
        GateRef::new(plonky2::gates::public_input::PublicInputGate {}),
        GateRef::new(plonky2::gates::base_sum::BaseSumGate::<2>::new_from_config::<F>(config)),
        GateRef::new(plonky2::gates::reducing_extension::ReducingExtensionGate::new(32)),
        GateRef::new(plonky2::gates::reducing::ReducingGate::new(43)),
        GateRef::new(
            plonky2::gates::arithmetic_extension::ArithmeticExtensionGate::new_from_config(config),
        ),
        GateRef::new(plonky2::gates::arithmetic_base::ArithmeticGate::new_from_config(config)),
        GateRef::new(
            plonky2::gates::multiplication_extension::MulExtensionGate::new_from_config(config),
        ),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 1)),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 2)),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 3)),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 4)),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 5)),
        GateRef::new(plonky2::gates::random_access::RandomAccessGate::new_from_config(config, 6)),
        GateRef::new(nnf_mul_simple.recursive_gate()),
        GateRef::new(nnf_mul_simple),
        GateRef::new(ec_add_homog_offset.recursive_gate()),
        GateRef::new(ec_add_homog_offset),
        GateRef::new(plonky2::gates::exponentiation::ExponentiationGate::new_from_config(config)),
        // It would be better do `CosetInterpolationGate::with_max_degree(4, 6)` but unfortunately
        // that plonk2 method is `pub(crate)`, so we need to get around that somehow.
        GateRef::new(coset_interpolation_gate(
            4,
            6,
            &[
                17293822565076172801,
                256,
                1048576,
                4294967296,
                17592186044416,
                72057594037927936,
                68719476720,
                281474976645120,
                1152921504338411520,
                18446744069414584065,
                18446744069413535745,
                18446744065119617025,
                18446726477228539905,
                18374686475376656385,
                18446744000695107601,
                18446462594437939201,
            ],
        )),
    ]
}

/// Estimate the number of gates to verify a proof of `degree_bits` that uses the
/// `standard_gates(&standard_recursion_config)`
fn estimate_verif_num_gates(degree_bits: usize) -> usize {
    let num_gates: usize;

    #[cfg(feature = "zk")]
    {
        // Formula obtained via linear regression using
        // `test_measure_zk_recursion` results with `standard_recursion_zk_config`.
        num_gates = 244 * degree_bits + 1127;
    }
    #[cfg(not(feature = "zk"))]
    {
        // Formula obtained via linear regression using `test_measure_recursion`
        // results with `standard_recursion_config`.
        num_gates = 236 * degree_bits + 1171;
    }
    // Add 2% for error because the results are not a clean line
    num_gates * 102 / 100
}

/// Estimate the number of gates after blinding (to add zk) and padding of a circuit with
/// `2^degree_bits` gates using `standard_recursion_zk_config`.
#[allow(dead_code)]
fn estimate_gates_after_zk(degree_bits: usize) -> usize {
    // Table data obtained using `test_measure_zk` results with `standard_recursion_zk_config`.
    match degree_bits {
        0..=12 => 1 << 14,
        13 => 1 << 15,
        n => 1 << (n + 1),
    }
}

// how many blinding gates are in this zk circuit
#[cfg(feature = "zk")]
fn blinding_gates(degree_bits: usize) -> usize {
    // Table data obtained using `test_measure_zk_recursion`, and printing
    // `regular_poly_openings + 2 * z_openings` at method `blind` of the file
    // `plonky2/plonky2/src/plonk/circuit_builder.rs`.
    match degree_bits {
        0..=12 => 8326,
        13..=14 => 8998,
        15 => 10342,
        16 => 13030,
        17 => 10846,
        _ => panic!("not supported"),
    }
}

pub fn common_data_for_recursion<I: InnerCircuit>(
    arity: usize,
    num_public_inputs: usize,
    inner_params: &I::Params,
) -> Result<CommonCircuitData<F, D>> {
    let config = CircuitConfig::standard_recursion_config();

    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    // Add our standard set of gates
    let standard_gates = standard_gates(&config);
    for gate in standard_gates.into_iter() {
        builder.add_gate_to_gate_set(gate);
    }

    let verified_proof = VerifiedProofTarget::add_virtual(&mut builder, num_public_inputs);
    let verified_proofs = (0..arity).map(|_| verified_proof.clone()).collect_vec();
    let _ = timed!(
        "common_data_for_recursion I::build",
        I::build(&mut builder, inner_params, &verified_proofs)?
    );
    let inner_num_gates = builder.num_gates();

    let circuit_data = timed!(
        "common_data_for_recursion builder.build",
        builder.build::<C>()
    );

    // Loop until we find a circuit size that can verify `arity` proofs of itself
    let mut degree_bits = log2_ceil(inner_num_gates);
    loop {
        let verif_num_gates = estimate_verif_num_gates(degree_bits);

        // Leave space for public input hashing, a `PublicInputGate` and some
        // `ConstantGate`s (that's MAX_CONSTANT_GATES*2 constants in the
        // standard_recursion_config).  And if the zk feature is enabled, add
        // space for the blinding gates.
        #[allow(unused_mut)]
        let mut total_num_gates = inner_num_gates
            + verif_num_gates * arity
            + circuit_data.common.num_public_inputs.div_ceil(8)
            + 1
            + MAX_CONSTANT_GATES;

        #[cfg(feature = "zk")]
        {
            total_num_gates += blinding_gates(degree_bits);
        }

        if total_num_gates < (1 << degree_bits) {
            break;
        }
        degree_bits = log2_ceil(total_num_gates);
    }

    let mut common_data = circuit_data.common.clone();
    common_data.fri_params.degree_bits = degree_bits;
    common_data.fri_params.reduction_arity_bits = vec![4, 4, 4];
    #[cfg(feature = "zk")]
    {
        common_data.fri_params.hiding = true;
        common_data.config.zero_knowledge = true;
    }
    Ok(common_data)
}

/// Pad the circuit to match a given `CommonCircuitData`.
pub fn pad_circuit(builder: &mut CircuitBuilder<F, D>, common_data: &CommonCircuitData<F, D>) {
    assert_eq!(common_data.config, builder.config);
    assert_eq!(common_data.num_public_inputs, builder.num_public_inputs());

    let degree = common_data.degree();
    // Need to account for public input hashing, a `PublicInputGate` and MAX_CONSTANT_GATES
    // `ConstantGate`. NOTE: the builder doesn't have any public method to see how many constants
    // have been registered, so we can't know exactly how many `ConstantGates` will be required.
    // We hope that no more than MAX_CONSTANT_GATES*2 constants are used :pray:.  Maybe we should
    // make a PR to plonky2 to expose this?
    #[allow(unused_mut)]
    let mut num_gates = degree - common_data.num_public_inputs.div_ceil(8) - 1 - MAX_CONSTANT_GATES;
    #[cfg(feature = "zk")]
    {
        // in the zk config case, account for the blinding gates, to avoid
        // padding to them too, because then plonky2's in the builder.build()
        // phase would add new blinding gates on top of the ones that we already
        // accounted for in the `common_data_for_recursion`, increasing (w.h.p.)
        // the degree of the circuit.
        num_gates -= blinding_gates(log2_ceil(degree));
    }

    assert!(
        builder.num_gates() < num_gates,
        "builder has more gates ({}) than the padding target ({})",
        builder.num_gates(),
        num_gates,
    );
    while builder.num_gates() < num_gates {
        builder.add_gate(NoopGate, vec![]);
    }
    for gate in &common_data.gates {
        builder.add_gate_to_gate_set(gate.clone());
    }
}

fn hash_verifier_data_gadget(
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

// compatible with hash_verifier_data_gadget.
pub fn hash_verifier_data(verifier_only_data: &VerifierOnlyCircuitData<C, D>) -> HashOut<F> {
    let f: Vec<F> = [
        verifier_only_data.circuit_digest.elements.to_vec(),
        verifier_only_data
            .constants_sigmas_cap
            .0
            .iter()
            .flat_map(|e| e.elements)
            .collect(),
    ]
    .concat();
    PoseidonHash::hash_no_pad(&f)
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
    use crate::{measure_gates_begin, measure_gates_end, measure_gates_print};

    // out-of-circuit input-output computation for Circuit1
    fn circuit1_io(inp: HashOut<F>) -> HashOut<F> {
        let mut aux: F = inp.elements[0];
        let two = F::from_canonical_u64(2u64);
        for _ in 0..5_000 {
            aux += two;
        }
        HashOut::<F>::from_vec(vec![aux, F::ZERO, F::ZERO, F::ZERO])
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
        let mut out: HashOut<F> = inp;
        for _ in 0..2000 {
            out = PoseidonHash::hash_no_pad(&out.elements)
        }
        out
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
            _verified_proofs: &[VerifiedProofTarget],
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();
            let mut aux: Target = input_targ.elements[0];
            let two = builder.constant(F::from_canonical_u64(2u64));
            for _ in 0..5_000 {
                aux = builder.add(aux, two);
            }
            let zero = builder.zero();
            let output_targ = HashOutTarget::from_vec(vec![aux, zero, zero, zero]);

            builder.register_public_inputs(output_targ.elements.as_ref());

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
            _verified_proofs: &[VerifiedProofTarget],
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();

            let mut output_targ: HashOutTarget = input_targ;
            for _ in 0..100 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            builder.register_public_inputs(output_targ.elements.as_ref());

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
            _verified_proofs: &[VerifiedProofTarget],
        ) -> Result<Self> {
            let input_targ = builder.add_virtual_hash();

            let mut output_targ: HashOutTarget = input_targ;
            for _ in 0..2000 {
                output_targ = builder
                    .hash_n_to_hash_no_pad::<PoseidonHash>(output_targ.elements.clone().to_vec());
            }

            builder.register_public_inputs(output_targ.elements.as_ref());

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
    fn test_inner_circuit_i() -> Result<()> {
        let inner_params = ();
        let inp = HashOut::<F>::ZERO;

        let inner_inputs = (inp, circuit1_io(inp));
        test_inner_circuit_i_opt::<Circuit1>(&inner_params, inner_inputs)?;

        let inner_inputs = (inp, circuit2_io(inp));
        test_inner_circuit_i_opt::<Circuit2>(&inner_params, inner_inputs)?;

        let inner_inputs = (inp, circuit3_io(inp));
        test_inner_circuit_i_opt::<Circuit3>(&inner_params, inner_inputs)?;

        Ok(())
    }
    fn test_inner_circuit_i_opt<IC: InnerCircuit>(
        inner_params: &IC::Params,
        inner_inputs: IC::Input,
    ) -> Result<()> {
        // circuit
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let mut pw = PartialWitness::<F>::new();

        let targets = IC::build(&mut builder, inner_params, &[])?;
        targets.set_targets(&mut pw, &inner_inputs)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof.clone())?;

        Ok(())
    }

    // Build an dummy empty circuit that uses common_data and make a proof from it.
    fn dummy(
        common_data: &CommonCircuitData<F, D>,
        num_public_inputs: usize,
    ) -> Result<(
        VerifierOnlyCircuitData<C, D>,
        ProofWithPublicInputs<F, C, D>,
    )> {
        let config = common_data.config.clone();
        let mut builder = CircuitBuilder::new(config.clone());

        let public_inputs = (0..num_public_inputs)
            .map(|_| {
                let target = builder.add_virtual_target();
                builder.register_public_input(target);
                target
            })
            .collect_vec();
        pad_circuit(&mut builder, common_data);

        let circuit_data = builder.build::<C>();
        assert_eq!(*common_data, circuit_data.common);

        let mut pw = PartialWitness::<F>::new();
        for target in &public_inputs {
            pw.set_target(*target, F::ZERO)?;
        }
        let proof = circuit_data.prove(pw)?;
        Ok((circuit_data.verifier_only, proof))
    }

    // test that recurses with arity=2, with the following shape:
    //          proof_1d
    //            ▲  ▲
    //          ┌─┘  └──┐
    //     proof_1b   proof2
    //       ▲  ▲       ▲  ▲
    //     ┌─┘  └─┐   ┌─┘  └─┐
    // proof_1a   0  proof3 proof_1c
    //
    #[test]
    fn test_recursive_circuit() -> Result<()> {
        let arity: usize = 2;
        let num_public_inputs: usize = 4;

        type RC<I> = RecursiveCircuit<I>;
        let inner_params = ();

        // build the circuit_data & verifier_data for the recursive circuit
        let start = Instant::now();
        let (_, circuit_data_3) =
            RC::<Circuit3>::target_and_circuit_data(arity, num_public_inputs, &inner_params)?;
        let params_3 = RecursiveParams {
            arity,
            common_data: circuit_data_3.common.clone(),
            verifier_data: circuit_data_3.verifier_data(),
        };
        let common_data = &circuit_data_3.common;

        let (_, circuit_data_1) =
            RC::<Circuit1>::target_and_circuit_data_padded(arity, &common_data, &inner_params)?;
        let params_1 = RecursiveParams {
            arity,
            common_data: circuit_data_1.common.clone(),
            verifier_data: circuit_data_1.verifier_data(),
        };

        let (_, circuit_data_2) =
            RC::<Circuit2>::target_and_circuit_data_padded(arity, &common_data, &inner_params)?;
        let params_2 = RecursiveParams {
            arity,
            common_data: circuit_data_2.common.clone(),
            verifier_data: circuit_data_2.verifier_data(),
        };

        println!(
            "new_params & (c1, c2, c3).circuit_data generated {:?}",
            start.elapsed()
        );

        let (dummy_verifier_data, dummy_proof) = dummy(common_data, num_public_inputs)?;

        let circuit1 = RC::<Circuit1>::build(&params_1, &())?;
        let circuit2 = RC::<Circuit2>::build(&params_2, &())?;
        let circuit3 = RC::<Circuit3>::build(&params_3, &())?;

        println!("circuit1.prove");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1a = circuit1.prove(
            &inner_inputs,
            vec![dummy_proof.clone(), dummy_proof.clone()],
            vec![dummy_verifier_data.clone(), dummy_verifier_data.clone()],
        )?;
        params_1.verifier_data.verify(proof_1a.clone())?;

        println!(
            "circuit1.prove (2nd iteration), verifies the proof of 1st iteration with circuit1"
        );
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1b = circuit1.prove(
            &inner_inputs,
            vec![proof_1a.clone(), dummy_proof.clone()],
            vec![
                params_1.verifier_data.verifier_only.clone(),
                dummy_verifier_data.clone(),
            ],
        )?;
        params_1.verifier_data.verify(proof_1b.clone())?;

        println!("circuit3.prove");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit3_io(inp));
        let proof_3 = circuit3.prove(
            &inner_inputs,
            vec![dummy_proof.clone(), dummy_proof.clone()],
            vec![dummy_verifier_data.clone(), dummy_verifier_data.clone()],
        )?;
        params_3.verifier_data.verify(proof_3.clone())?;

        println!("circuit1.prove");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1c = circuit1.prove(
            &inner_inputs,
            vec![dummy_proof.clone(), dummy_proof.clone()],
            vec![dummy_verifier_data.clone(), dummy_verifier_data.clone()],
        )?;
        params_1.verifier_data.verify(proof_1c.clone())?;

        // generate a proof of Circuit2, which internally verifies the proof_3 & proof_1c
        println!("circuit2.prove, which internally verifies the proof_3 & proof_1c");
        let inner_inputs = (inp, circuit2_io(inp));
        let proof_2 = circuit2.prove(
            &inner_inputs,
            vec![proof_3.clone(), proof_1c],
            vec![
                params_3.verifier_data.verifier_only.clone(),
                params_1.verifier_data.verifier_only.clone(),
            ],
        )?;
        params_2.verifier_data.verify(proof_2.clone())?;

        // verify the last proof of circuit2, inside a new circuit1's proof
        println!("proof_1d = c1.prove([proof_1b, proof_2], [verifier_data_1, verifier_data_2])");
        let inp = HashOut::<F>::ZERO;
        let inner_inputs = (inp, circuit1_io(inp));
        let proof_1d = circuit1.prove(
            &inner_inputs,
            vec![proof_1b, proof_2],
            vec![
                params_1.verifier_data.verifier_only.clone(),
                params_2.verifier_data.verifier_only.clone(),
            ],
        )?;
        params_1.verifier_data.verify(proof_1d)?;

        Ok(())
    }

    #[ignore]
    #[test]
    fn test_measure_recursion() {
        let config = CircuitConfig::standard_recursion_config();
        for i in 7..20 {
            let mut builder = CircuitBuilder::new(config.clone());
            let standard_gates = standard_gates(&config);
            for gate in standard_gates.into_iter() {
                builder.add_gate_to_gate_set(gate);
            }
            while builder.num_gates() < (1 << i) - MAX_CONSTANT_GATES {
                builder.add_gate(NoopGate, vec![]);
            }
            println!("build degree 2^{} ...", i);
            let circuit_data = builder.build::<C>();
            assert_eq!(i, circuit_data.common.degree_bits());

            let mut builder = CircuitBuilder::new(config.clone());
            let measure = measure_gates_begin!(&builder, format!("verifier for 2^{}", i));
            let verifier_data_i =
                builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);
            let proof = builder.add_virtual_proof_with_pis(&circuit_data.common);
            builder.verify_proof::<C>(&proof, &verifier_data_i, &circuit_data.common);
            measure_gates_end!(&builder, measure);
        }
        measure_gates_print!();
    }

    #[ignore]
    #[test]
    fn test_measure_zk() {
        let config = CircuitConfig::standard_recursion_zk_config();
        for i in 7..18 {
            let mut builder = CircuitBuilder::new(config.clone());
            builder.add_gate_to_gate_set(plonky2::gates::gate::GateRef::new(
                plonky2::gates::constant::ConstantGate::new(config.num_constants),
            ));
            while builder.num_gates() < (1 << i) - MAX_CONSTANT_GATES {
                builder.add_gate(NoopGate, vec![]);
            }
            let circuit_data = builder.build::<C>();
            println!(
                "2^{} gates require 2^{} rows",
                i,
                circuit_data.common.degree_bits()
            );
        }
    }

    #[ignore]
    #[test]
    fn test_measure_zk_recursion() {
        let config = CircuitConfig::standard_recursion_zk_config();
        for i in 12..18 {
            let mut builder = CircuitBuilder::new(config.clone());
            let standard_gates = standard_gates(&config);
            for gate in standard_gates.into_iter() {
                builder.add_gate_to_gate_set(gate);
            }
            while builder.num_gates() < (1 << i) - MAX_CONSTANT_GATES {
                builder.add_gate(NoopGate, vec![]);
            }
            let expected_degree_bits = log2_ceil(estimate_gates_after_zk(i));
            println!("build degree 2^{} ...", i);
            let circuit_data = builder.build::<C>();
            assert_eq!(expected_degree_bits, circuit_data.common.degree_bits());

            let mut builder = CircuitBuilder::new(config.clone());
            let measure = measure_gates_begin!(
                &builder,
                format!("verifier for zk 2^{}", expected_degree_bits)
            );
            let verifier_data_i =
                builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);
            let proof = builder.add_virtual_proof_with_pis(&circuit_data.common);
            builder.verify_proof::<C>(&proof, &verifier_data_i, &circuit_data.common);
            measure_gates_end!(&builder, measure);
        }
        measure_gates_print!();
    }
}
