use std::{
    any::Any,
    collections::HashMap,
    iter,
    sync::{Arc, LazyLock, MappedRwLockReadGuard, RwLock, RwLockReadGuard},
};

use base64::{prelude::BASE64_STANDARD, Engine};
use itertools::Itertools;
use num::bigint::BigUint;
use plonky2::{
    field::{
        extension::Extendable,
        secp256k1_scalar::Secp256K1Scalar,
        types::{PrimeField64, Sample},
    },
    gates::noop::NoopGate,
    hash::{
        hash_types::{HashOut, HashOutTarget, RichField},
        poseidon::PoseidonHash,
    },
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{
            CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData,
            VerifierOnlyCircuitData,
        },
        config::Hasher,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    util::serialization::{Buffer, Read},
};
use plonky2_ecdsa::{
    curve::{
        curve_types::{Curve, CurveScalar},
        ecdsa::{sign_message, verify_message, ECDSAPublicKey, ECDSASecretKey, ECDSASignature},
        secp256k1::Secp256K1,
    },
    gadgets::{
        biguint::{BigUintTarget, CircuitBuilderBiguint, GeneratedValuesBigUint, WitnessBigUint},
        curve::{AffinePointTarget, CircuitBuilderCurve},
        ecdsa::{verify_message_circuit, ECDSAPublicKeyTarget, ECDSASignatureTarget},
        nonnative::{CircuitBuilderNonNative, NonNativeTarget},
    },
};

use crate::{
    backends::plonky2::{
        basetypes::{Proof, C, D},
        circuits::{
            common::{
                CircuitBuilderPod, Flattenable, PredicateTarget, StatementArgTarget,
                StatementTarget, ValueTarget,
            },
            mainpod::{
                CalculateIdGadget, CustomPredicateVerification, MainPodVerifyCircuit,
                MainPodVerifyInput, MainPodVerifyTarget, NUM_PUBLIC_INPUTS, PI_OFFSET_ID,
            },
        },
        error::{Error, Result},
        mainpod,
        mainpod::calculate_id,
        primitives::{
            merkletree::{
                MerkleClaimAndProof, MerkleProofExistenceGadget, MerkleProofExistenceTarget,
                MerkleTree,
            },
            signature::{
                PublicKey, SecretKey, Signature, SignatureVerifyGadget, SignatureVerifyTarget, VP,
            },
        },
        recursion::{
            self, common_data_for_recursion, InnerCircuit, RecursiveCircuit, RecursiveParams,
            VerifiedProofTarget,
        },
        signedpod::SignedPod,
    },
    constants::MAX_DEPTH,
    measure_gates_begin, measure_gates_end,
    middleware::{
        self, containers::Dictionary, hash_str, resolve_wildcard_values, AnchoredKey,
        CustomPredicateBatch, DynError, Hash, Key, MainPodInputs, NativeOperation, NativePredicate,
        NonePod, OperationType, Params, Pod, PodId, PodProver, PodSigner, PodType, RawValue,
        Statement, StatementArg, ToFields, Value, EMPTY_HASH, EMPTY_VALUE, F, HASH_SIZE,
        KEY_SIGNER, KEY_TYPE, SELF,
    },
    timed,
};

// TODO better naming
static ECDSA_VERIFIER_DATA: LazyLock<(EcdsaVerifierTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ecdsa_verifier().expect("successful build"));

// TODO better naming
fn build_ecdsa_verifier() -> Result<(EcdsaVerifierTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_verify_target = EcdsaVerifierTarget::add_targets(&mut builder)?;

    let data = timed!("EcdsaVerifier build", builder.build::<C>());
    Ok((ecdsa_verify_target, data))
}

// Note: this circuit requires the CircuitConfig's standard_ecc_config or
// wide_ecc_config.
struct EcdsaVerifierTarget {
    msg: NonNativeTarget<Secp256K1Scalar>,
    pk: ECDSAPublicKeyTarget<Secp256K1>,
    signature: ECDSASignatureTarget<Secp256K1>,
}

impl EcdsaVerifierTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "SignedPodVerify");
        let msg = builder.add_virtual_nonnative_target::<Secp256K1Scalar>();
        let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<Secp256K1>());
        let r = builder.add_virtual_nonnative_target();
        let s = builder.add_virtual_nonnative_target();
        let sig = ECDSASignatureTarget::<Secp256K1> { r, s };

        // TODO uncomment
        // verify_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // TODO
        // builder.register_public_inputs(&pk);
        // builder.register_public_inputs(&msg);

        measure_gates_end!(builder, measure);
        Ok(EcdsaVerifierTarget {
            msg,
            pk,
            signature: sig,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        msg: Secp256K1Scalar,
        pk: ECDSAPublicKey<Secp256K1>,
        signature: ECDSASignature<Secp256K1>,
    ) -> Result<()> {
        pw.set_biguint_target(
            &self.msg.value,
            &biguint_from_array(std::array::from_fn(|i| msg.0[i])),
        )?;
        pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(pk.0.x.0))?;
        pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(pk.0.y.0))?;
        pw.set_biguint_target(&self.signature.r.value, &biguint_from_array(signature.r.0))?;
        pw.set_biguint_target(&self.signature.s.value, &biguint_from_array(signature.s.0))?;

        Ok(())
    }
}
struct EcdsaPodVerifyTarget {
    params: Params, // TODO rm?
    vds_root: HashOutTarget,
    id: HashOutTarget,
    // msg: NonNativeTarget<Secp256K1Scalar>,
    // pk: ECDSAPublicKeyTarget<Secp256K1>,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct EcdsaPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    // msg: Secp256K1Scalar,
    // pk: ECDSAPublicKey<Secp256K1>,
    proof: ProofWithPublicInputs<F, C, D>,
}
impl InnerCircuit for EcdsaPodVerifyTarget {
    type Input = EcdsaPodVerifyInput;
    type Params = Params;

    fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &Params,
        _verified_proofs: &[VerifiedProofTarget],
    ) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "EcdsaPodVerifyTarget");
        // 1. Verify id
        let statements: Vec<StatementTarget> = pub_self_statements()
            .iter()
            .map(|statement| {
                StatementTarget::from_flattened(
                    &params,
                    &builder.constants(&statement.to_fields(&params)),
                )
            })
            .collect();
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements);

        // 2. Verify  EcdsaVerifierTarget's proof (with verifier_data hardcoded
        //    as constant)
        let (_, circuit_data) = &*ECDSA_VERIFIER_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        for pi in proof_targ.public_inputs.iter() {
            builder.register_public_input(*pi);
        }

        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);

        measure_gates_end!(builder, measure);
        Ok(EcdsaPodVerifyTarget {
            params: params.clone(),
            vds_root,
            id,
            // msg,
            // pk,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &EcdsaPodVerifyInput) -> Result<()> {
        // set signature targets values
        // pw.set_biguint_target(
        //     &self.msg.value,
        //     &biguint_from_array(std::array::from_fn(|i| input.msg.0[i])),
        // )?;
        // pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(input.pk.0.x.0))?;
        // pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(input.pk.0.y.0))?;

        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;

        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0 .0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

static STANDARD_ECDSA_POD_DATA: LazyLock<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

/// build the circuit of EcdsaPodVerifyCircuit, padded to the amount of gates
/// needed to make it compatible with the RecursiveCircuit
fn build() -> Result<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*crate::backends::plonky2::DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_pod_verify_target = EcdsaPodVerifyTarget::build(&mut builder, params, &[])?;
    let circuit_data = &*crate::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    crate::backends::plonky2::recursion::pad_circuit(&mut builder, &circuit_data.common);

    let data = timed!("EcdsaPod build", builder.build::<C>());
    assert_eq!(circuit_data.common, data.common);
    Ok((ecdsa_pod_verify_target, data))
}

#[derive(Clone, Debug)]
pub struct EcdsaPod {
    params: Params,
    id: PodId,
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
    signature: ECDSASignature<Secp256K1>,
    proof: Proof,
    vds_hash: Hash,
    verifier_data: VerifierOnlyCircuitData<C, D>,
}
impl middleware::RecursivePod for EcdsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        // TODO: rm 'verifier_data' field, and 'compute' it with the 'build'
        // method, so that the method 'EcdsaPod.verifier_data()' can get it
        // from there and not from an internal field
        self.verifier_data.clone()
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
    }
}

impl EcdsaPod {
    fn _prove(
        params: &Params,
        vds_root: Hash,
        msg: Secp256K1Scalar,
        sk: ECDSASecretKey<Secp256K1>,
    ) -> Result<EcdsaPod> {
        // 1. sign the pod id
        let pk: ECDSAPublicKey<Secp256K1> =
            ECDSAPublicKey((CurveScalar(sk.0) * Secp256K1::GENERATOR_PROJECTIVE).to_affine());
        let signature: ECDSASignature<Secp256K1> = sign_message(msg, sk);

        // 2. prove the EcdsaVerify circuit
        let (ecdsa_verify_target, ecdsa_circuit_data) = &*ECDSA_VERIFIER_DATA;
        let mut pw = PartialWitness::<F>::new();
        ecdsa_verify_target.set_targets(&mut pw, msg, pk, signature)?;

        let ecdsa_verify_proof = ecdsa_circuit_data.prove(pw)?;

        // 3. verify the ecdsa_verify proof in a EcdsaPodVerifyTarget circuit

        let rec_circuit_data = &*crate::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
        // println!("DBG recursive MainPod build BEGIN");
        let (ecdsa_pod_target, circuit_data) =
            RecursiveCircuit::<EcdsaPodVerifyTarget>::circuit_data_padded(
                params.max_input_recursive_pods,
                &rec_circuit_data.common,
                params,
            )?;
        let rec_params = RecursiveParams {
            arity: params.max_input_recursive_pods,
            common_data: circuit_data.common.clone(),
            verifier_data: circuit_data.verifier_data(),
        };
        let ecdsa_pod = RecursiveCircuit::<EcdsaPodVerifyTarget> {
            params: rec_params.clone(),
            prover: circuit_data.prover_data(),
            target: ecdsa_pod_target,
        };

        // now that sig is done, gen a plonky2 proof of the circuit that verifies it

        let statements = pub_self_statements()
            .into_iter()
            .map(|st| mainpod::Statement::from(st))
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // set targets
        dbg!("A 4");
        let input = EcdsaPodVerifyInput {
            vds_root,
            id,
            proof: ecdsa_verify_proof,
            // msg: msg.clone(),
            // pk,
        };
        let (dummy_verifier_data, dummy_proof) =
            crate::backends::plonky2::recursion::circuit::dummy(
                &rec_params.common_data,
                NUM_PUBLIC_INPUTS, // TODO num_public_inputs,
            )?;
        dbg!("A 5");
        let proof_with_pis = ecdsa_pod.prove(
            &input,
            vec![dummy_proof.clone(), dummy_proof.clone()],
            vec![dummy_verifier_data.clone(), dummy_verifier_data.clone()],
        )?;
        dbg!("A 6");

        #[cfg(test)] // sanity check
        {
            let (_, circuit_data) = RecursiveCircuit::<EcdsaPodVerifyTarget>::circuit_data_padded(
                params.max_input_recursive_pods,
                &rec_circuit_data.common,
                params,
            )?;
            circuit_data
                .verifier_data()
                .verify(proof_with_pis.clone())?;
        }
        dbg!("A 7");

        Ok(EcdsaPod {
            params: params.clone(),
            id,
            msg,
            pk,
            signature,
            proof: proof_with_pis.proof,
            vds_hash: EMPTY_HASH,
            // TODO: rm 'verifier_data' field, and 'compute' it with the 'build'
            // method, so that the method 'EcdsaPod.verifier_data()' can get it
            // from there and not from an internal field
            verifier_data: rec_params.verifier_data().verifier_only.clone(),
        })
    }
    fn new(
        params: &Params,
        vds_root: Hash,
        msg: Secp256K1Scalar,
        sk: ECDSASecretKey<Secp256K1>,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        // TODO move _prove contents directly here, no need to abstract method
        Ok(Self::_prove(params, vds_root, msg, sk).map(Box::new)?)
    }
    fn _verify(&self) -> Result<()> {
        dbg!("B 0");
        let statements = pub_self_statements()
            .into_iter()
            .map(|st| mainpod::Statement::from(st))
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }
        dbg!("B 1");

        let rec_circuit_data = &*crate::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
        // TODO: cache these artefacts
        let (_, circuit_data) = RecursiveCircuit::<EcdsaPodVerifyTarget>::circuit_data_padded(
            self.params.max_input_recursive_pods,
            &rec_circuit_data.common,
            &self.params,
        )?;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(EMPTY_HASH.0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

        dbg!("B 2");
        circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("EcdsaPod proof verification failure: {:?}", e)))
    }
}
impl Pod for EcdsaPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify().map_err(Box::new)?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        pub_self_statements() // (self.pk)
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

fn type_statement() -> Statement {
    Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_TYPE)),
        Value::from(PodType::Main),
        // TODO PodType::Main? should we rename it to Recursive? or define a
        // new type PodType::Recursive?
    )
}
fn pub_self_statements() -> Vec<middleware::Statement> {
    vec![type_statement()]
    // TODO: statement for pk
}

fn biguint_from_array(arr: [u64; 4]) -> BigUint {
    BigUint::from_slice(&[
        arr[0] as u32,
        (arr[0] >> 32) as u32,
        arr[1] as u32,
        (arr[1] >> 32) as u32,
        arr[2] as u32,
        (arr[2] >> 32) as u32,
        arr[3] as u32,
        (arr[3] >> 32) as u32,
    ])
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use plonky2::plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig};

    use super::*;
    use crate::{
        backends::plonky2::{
            basetypes::C,
            primitives::signature::SecretKey,
            signedpod::{SignedPod, Signer},
        },
        frontend::MainPodBuilder,
        middleware::F,
        op,
    };

    #[test]
    fn test_ecdsa_pod_verify() -> Result<()> {
        let params = Params {
            max_input_signed_pods: 0,
            max_input_recursive_pods: 2,
            max_signed_pod_values: 6,
            num_public_statements_id: 16,
            ..Default::default()
        };

        let msg = Secp256K1Scalar::rand();
        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar::rand());
        let vds_root = EMPTY_HASH;
        let ecdsa_pod = EcdsaPod::new(&params, vds_root, msg, sk).unwrap();
        dbg!("ecdsapod generated");

        ecdsa_pod.verify().unwrap();

        // wrap the ecdsa_pod in a 'MainPod' (RecursivePod)
        let main_ecdsa_pod = crate::frontend::MainPod {
            pod: (ecdsa_pod.clone() as Box<dyn Any>)
                .downcast::<EcdsaPod>()
                .unwrap(),
            public_statements: ecdsa_pod.pub_statements(), // TODO WIP
            params: params.clone(),
        };

        // now generate a new MainPod from the ecdsa_pod
        let mut main_pod_builder = MainPodBuilder::new(&params);
        main_pod_builder.add_main_pod(main_ecdsa_pod);

        // let now_minus_18y: i64 = 1169909388;
        // main_pod_builder
        //     .pub_op(op!(lt, (&ecdsa_pod, "dateOfBirth"), now_minus_18y))
        //     .unwrap();

        // emptypod
        let empty_pod: Box<dyn middleware::RecursivePod> =
            crate::backends::plonky2::emptypod::EmptyPod::new_boxed(&params, EMPTY_HASH);
        let main_empty_pod = crate::frontend::MainPod {
            pod: empty_pod.clone(),
            public_statements: empty_pod.pub_statements(),
            params: params.clone(),
        };
        main_pod_builder.add_main_pod(main_empty_pod);

        let mut prover = crate::backends::plonky2::mock::mainpod::MockProver {};
        let pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        assert!(pod.pod.verify().is_ok());

        println!("going to prove the main_pod");
        let mut prover = mainpod::Prover {};
        let main_pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        let pod = (main_pod.pod as Box<dyn Any>)
            .downcast::<mainpod::MainPod>()
            .unwrap();
        pod.verify().unwrap();

        Ok(())
    }
}
