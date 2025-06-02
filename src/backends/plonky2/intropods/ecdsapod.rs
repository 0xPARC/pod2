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
        secp256k1_base::Secp256K1Base,
        secp256k1_scalar::Secp256K1Scalar,
        types::{Field, PrimeField, PrimeField64, Sample},
    },
    gates::noop::NoopGate,
    hash::{
        hash_types::{HashOut, HashOutTarget, RichField},
        poseidon::PoseidonHash,
    },
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
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
            self, circuit::RecursiveCircuitTarget, common_data_for_recursion, InnerCircuit,
            RecursiveCircuit, RecursiveParams, VerifiedProofTarget,
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

pub const ECDSA_POD_NUM_PUBLIC_INPUTS: usize = NUM_PUBLIC_INPUTS + 8;
const KEY_SIGNED_MSG: &str = "signed_msg";
const KEY_ECDSA_PK: &str = "ecdsa_pk";

// TODO better naming
static ECDSA_VERIFY_DATA: LazyLock<(EcdsaVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build_ecdsa_verify().expect("successful build"));

fn build_ecdsa_verify() -> Result<(EcdsaVerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_verify_target = EcdsaVerifyTarget::add_targets(&mut builder)?;

    let data = timed!("EcdsaVerify build", builder.build::<C>());
    Ok((ecdsa_verify_target, data))
}

// Note: this circuit requires the CircuitConfig's standard_ecc_config or
// wide_ecc_config.
struct EcdsaVerifyTarget {
    msg: NonNativeTarget<Secp256K1Scalar>,
    pk: ECDSAPublicKeyTarget<Secp256K1>,
    signature: ECDSASignatureTarget<Secp256K1>,
}

impl EcdsaVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "EcdsaVerifyTarget");
        let msg = builder.add_virtual_nonnative_target::<Secp256K1Scalar>();
        let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<Secp256K1>());
        let r = builder.add_virtual_nonnative_target();
        let s = builder.add_virtual_nonnative_target();
        let sig = ECDSASignatureTarget::<Secp256K1> { r, s };

        // TODO uncomment
        verify_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // register public inputs
        for l in msg.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        // register pk as public input
        for l in pk.0.x.value.limbs.iter() {
            builder.register_public_input(l.0);
        }
        for l in pk.0.y.value.limbs.iter() {
            builder.register_public_input(l.0);
        }

        measure_gates_end!(builder, measure);
        // crate::measure_gates_print!();
        Ok(EcdsaVerifyTarget {
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

#[derive(Clone, Debug)]
struct EcdsaPodVerifyTarget {
    vds_root: HashOutTarget,
    id: HashOutTarget,
    proof: ProofWithPublicInputsTarget<D>,
}

pub struct EcdsaPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    proof: ProofWithPublicInputs<F, C, D>,
}
impl EcdsaPodVerifyTarget {
    fn add_targets(builder: &mut CircuitBuilder<F, D>, params: &Params) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "EcdsaPodVerifyTarget");

        // Verify EcdsaVerifyTarget's proof (with verifier_data hardcoded as constant)
        let (_, circuit_data) = &*ECDSA_VERIFY_DATA;
        let verifier_data_targ = builder.constant_verifier_data(&circuit_data.verifier_only);
        let proof_targ = builder.add_virtual_proof_with_pis(&circuit_data.common);
        builder.verify_proof::<C>(&proof_targ, &verifier_data_targ, &circuit_data.common);

        // calculate id
        let msg = &proof_targ.public_inputs[0..8];
        let pk = &proof_targ.public_inputs[8..24];
        let statements = pub_self_statements_target(builder, params, msg, pk);
        let id = CalculateIdGadget {
            params: params.clone(),
        }
        .eval(builder, &statements); // TODO st_pk

        // register the public inputs
        let vds_root = builder.add_virtual_hash();
        builder.register_public_inputs(&id.elements);
        builder.register_public_inputs(&vds_root.elements);

        measure_gates_end!(builder, measure);
        // crate::measure_gates_print!();
        Ok(EcdsaPodVerifyTarget {
            vds_root,
            id,
            proof: proof_targ,
        })
    }

    fn set_targets(&self, pw: &mut PartialWitness<F>, input: &EcdsaPodVerifyInput) -> Result<()> {
        pw.set_proof_with_pis_target(&self.proof, &input.proof)?;
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0 .0.to_vec()))?;
        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct EcdsaPod {
    params: Params,
    id: PodId,
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
    proof: Proof,
    vds_hash: Hash,
}
impl middleware::RecursivePod for EcdsaPod {
    fn verifier_data(&self) -> VerifierOnlyCircuitData<C, D> {
        let (_, circuit_data) = &*STANDARD_ECDSA_POD_DATA;
        circuit_data.verifier_data().verifier_only
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vds_root(&self) -> Hash {
        self.vds_hash
    }
}

static STANDARD_ECDSA_POD_DATA: LazyLock<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> =
    LazyLock::new(|| build().expect("successful build"));

fn build() -> Result<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let params = &*crate::backends::plonky2::DEFAULT_PARAMS;
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let ecdsa_pod_verify_target = EcdsaPodVerifyTarget::add_targets(&mut builder, params)?;
    let rec_circuit_data = &*crate::backends::plonky2::STANDARD_REC_MAIN_POD_CIRCUIT_DATA;
    crate::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_circuit_data.common);

    let data = timed!("EcdsaPod build", builder.build::<C>());
    assert_eq!(rec_circuit_data.common, data.common);
    Ok((ecdsa_pod_verify_target, data))
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
        let (ecdsa_verify_target, ecdsa_circuit_data) = &*ECDSA_VERIFY_DATA;
        let mut pw = PartialWitness::<F>::new();
        ecdsa_verify_target.set_targets(&mut pw, msg, pk, signature)?;

        let ecdsa_verify_proof = timed!(
            "prove the ecdsa signature verification (EcdsaVerifyTarget)",
            ecdsa_circuit_data.prove(pw)?
        );

        // 3. verify the ecdsa_verify proof in a EcdsaPodVerifyTarget circuit

        let (ecdsa_pod_target, circuit_data) = &*STANDARD_ECDSA_POD_DATA;

        let statements = pub_self_statements(msg, pk)
            .into_iter()
            .map(|st| mainpod::Statement::from(st))
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, params));

        // set targets
        let input = EcdsaPodVerifyInput {
            vds_root,
            id,
            proof: ecdsa_verify_proof,
        };
        let mut pw = PartialWitness::<F>::new();
        ecdsa_pod_target.set_targets(&mut pw, &input)?;
        let proof_with_pis = timed!(
            "prove the ecdsa-verification proof verification (EcdsaPod proof)",
            circuit_data.prove(pw)?
        );

        #[cfg(test)] // sanity check
        {
            circuit_data
                .verifier_data()
                .verify(proof_with_pis.clone())?;
        }

        Ok(EcdsaPod {
            params: params.clone(),
            id,
            msg,
            pk,
            proof: proof_with_pis.proof,
            vds_hash: EMPTY_HASH,
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
        let statements = pub_self_statements(self.msg, self.pk)
            .into_iter()
            .map(|st| mainpod::Statement::from(st))
            .collect_vec();
        let id: PodId = PodId(calculate_id(&statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        let (_, circuit_data) = &*STANDARD_ECDSA_POD_DATA;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(EMPTY_HASH.0.iter()) // slot for the unused vds root
            .cloned()
            .collect_vec();

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
        pub_self_statements(self.msg, self.pk)
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
        Value::from(1001), // TODO define new type Ecdsa
    )
}

fn pub_self_statements_target(
    builder: &mut CircuitBuilder<F, D>,
    params: &Params,
    msg: &[Target],
    pk: &[Target],
) -> Vec<StatementTarget> {
    let ak_podid = builder.constant_value(RawValue::from(SELF.0));

    let msg_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(msg.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_SIGNED_MSG).raw());
    let ak_msg = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&msg_hash.elements));
    let st_msg =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_msg, value]);

    let pk_hash = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pk.to_vec());
    let ak_key = builder.constant_value(Key::from(KEY_ECDSA_PK).raw());
    let ak_pk = StatementArgTarget::anchored_key(builder, &ak_podid, &ak_key);
    let value = StatementArgTarget::literal(builder, &ValueTarget::from_slice(&pk_hash.elements));
    let st_pk =
        StatementTarget::new_native(builder, params, NativePredicate::ValueOf, &[ak_pk, value]);

    let st_type = StatementTarget::from_flattened(
        &params,
        &builder.constants(&type_statement().to_fields(&params)),
    );
    vec![st_type, st_msg, st_pk]
}

// compatibel with the same method in-circuit (pub_self_statements_target)
fn pub_self_statements(
    msg: Secp256K1Scalar,
    pk: ECDSAPublicKey<Secp256K1>,
) -> Vec<middleware::Statement> {
    // hash the msg as in-circuit
    let msg_limbs = scalar_to_limbs(msg);
    let msg_hash = PoseidonHash::hash_no_pad(&msg_limbs);

    let st_msg = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_SIGNED_MSG)),
        Value::from(RawValue(msg_hash.elements)),
    );

    let pk_x_limbs = base_to_limbs(pk.0.x);
    let pk_y_limbs = base_to_limbs(pk.0.y);
    let pk_hash = PoseidonHash::hash_no_pad(&[pk_x_limbs, pk_y_limbs].concat());

    let st_pk = Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_ECDSA_PK)),
        Value::from(RawValue(pk_hash.elements)),
    );

    let st_type = type_statement();

    vec![st_type, st_msg, st_pk]
}
fn scalar_to_limbs(v: Secp256K1Scalar) -> Vec<F> {
    let max_num_limbs = 8;
    let v_biguint = biguint_from_array(std::array::from_fn(|i| v.0[i]));
    let mut limbs = v_biguint.to_u32_digits();
    assert!(max_num_limbs >= limbs.len());
    limbs.resize(max_num_limbs, 0);
    let limbs_f: Vec<F> = limbs.iter().map(|l| F::from_canonical_u32(*l)).collect();
    limbs_f
}
fn base_to_limbs(v: Secp256K1Base) -> Vec<F> {
    let max_num_limbs = 8;
    let v_biguint = biguint_from_array(std::array::from_fn(|i| v.0[i]));
    let mut limbs = v_biguint.to_u32_digits();
    assert!(max_num_limbs >= limbs.len());
    limbs.resize(max_num_limbs, 0);
    let limbs_f: Vec<F> = limbs.iter().map(|l| F::from_canonical_u32(*l)).collect();
    limbs_f
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

    #[ignore] // skip this test by default, since it takes >100s to run
    #[test]
    fn test_ecdsa_pod_verify() -> Result<()> {
        let params = Params {
            max_input_signed_pods: 0,
            ..Default::default()
        };

        let msg = Secp256K1Scalar::rand();
        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar::rand());
        let vds_root = EMPTY_HASH;
        let ecdsa_pod = timed!(
            "EcdsaPod::new",
            EcdsaPod::new(&params, vds_root, msg, sk).unwrap()
        );

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
