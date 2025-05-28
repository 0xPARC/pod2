use std::{any::Any, collections::HashMap, iter, sync::Arc};

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
        circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData},
        config::Hasher,
        proof::ProofWithPublicInputs,
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
            self, common_data_for_recursion, InnerCircuit, RecursiveCircuit, VerifiedProofTarget,
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
};

struct EcdsaPodVerifyTarget {
    params: Params,
    vds_root: HashOutTarget,
    id: HashOutTarget,
    // msg: NonNativeTarget<Secp256K1Scalar>,
    // pk: ECDSAPublicKeyTarget<Secp256K1>,
    // signature: ECDSASignatureTarget<Secp256K1>,

    // the KEY_TYPE entry must be the first one
    // the KEY_SIGNER entry must be the second one
    mt_proofs: Vec<MerkleProofExistenceTarget>,
}

pub struct EcdsaPodVerifyInput {
    vds_root: Hash,
    id: PodId,
    // pk: ECDSAPublicKey<Secp256K1>,
    dict: Dictionary,
    // signature: ECDSASignature<Secp256K1>,
}
impl InnerCircuit for EcdsaPodVerifyTarget {
    type Input = EcdsaPodVerifyInput;
    type Params = Params;

    fn build(
        builder: &mut CircuitBuilder<F, D>,
        params: &Params,
        _verified_proofs: &[VerifiedProofTarget],
    ) -> Result<Self> {
        let measure = measure_gates_begin!(builder, "SignedPodVerify");
        // 1. Verify id
        let id = builder.add_virtual_hash();
        let mut mt_proofs = Vec::new();
        for _ in 0..params.max_signed_pod_values {
            let mt_proof = MerkleProofExistenceGadget {
                max_depth: params.max_depth_mt_gadget,
            }
            .eval(builder)?;
            builder.connect_hashes(id, mt_proof.root);
            mt_proofs.push(mt_proof);
        }

        // 2. Verify type
        let type_mt_proof = &mt_proofs[0];
        let key_type = builder.constant_value(hash_str(KEY_TYPE).into());
        builder.connect_values(type_mt_proof.key, key_type);
        let value_type = builder.constant_value(Value::from(PodType::Signed).raw());
        builder.connect_values(type_mt_proof.value, value_type);

        // 3.a. Verify signature
        // let msg = builder.add_virtual_nonnative_target::<Secp256K1Scalar>();
        // let pk = ECDSAPublicKeyTarget(builder.add_virtual_affine_point_target::<Secp256K1>());
        // let r = builder.add_virtual_nonnative_target();
        // let s = builder.add_virtual_nonnative_target();
        // let sig = ECDSASignatureTarget::<Secp256K1> { r, s };
        //
        // verify_message_circuit(builder, msg.clone(), sig.clone(), pk.clone());

        // 3.b. Verify signer (ie. signature.pk == merkletree.signer_leaf)
        // TODO

        // 3.c. connect signed message to pod.id
        // TODO maybe relate them through some hash
        // builder.connect_values(ValueTarget::from_slice(&id.elements), msg);

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
            // signature: sig,
            mt_proofs,
        })
    }

    fn set_targets(
        &self,
        pw: &mut PartialWitness<F>,
        input: &EcdsaPodVerifyInput,
        // vds_root: Hash,
        // id: PodId,
        // pk: ECDSAPublicKey<Secp256K1>,
        // dict: Dictionary,
        // signature: ECDSASignature<Secp256K1>,
    ) -> Result<()> {
        // set the self.mt_proofs witness with the following order:
        // - KEY_TYPE leaf proof
        // - KEY_SIGNER leaf proof
        // - rest of leaves
        // - empty leaves (if needed)

        // add proof verification of KEY_TYPE & KEY_SIGNER leaves
        let key_type_key = Key::from(KEY_TYPE);
        let key_signer_key = Key::from(KEY_SIGNER);
        let key_signer_value = [&key_type_key, &key_signer_key]
            .iter()
            .enumerate()
            .map(|(i, k)| {
                let (v, proof) = input.dict.prove(k)?;
                self.mt_proofs[i].set_targets(
                    pw,
                    true,
                    &MerkleClaimAndProof::new(
                        input.dict.commitment(),
                        k.raw(),
                        Some(v.raw()),
                        proof,
                    ),
                )?;
                Ok(v)
            })
            .collect::<Result<Vec<&Value>>>()?[1];

        // add the verification of the rest of leaves
        let mut curr = 2; // since we already added key_type and key_signer
        for (k, v) in input.dict.kvs().iter().sorted_by_key(|kv| kv.0.hash()) {
            if *k == key_type_key || *k == key_signer_key {
                // skip the key_type & key_signer leaves, since they have
                // already been checked
                continue;
            }

            let (obtained_v, proof) = input.dict.prove(k)?;
            assert_eq!(obtained_v, v); // sanity check

            self.mt_proofs[curr].set_targets(
                pw,
                true,
                &MerkleClaimAndProof::new(input.dict.commitment(), k.raw(), Some(v.raw()), proof),
            )?;
            curr += 1;
        }
        // sanity check
        assert!(curr <= self.params.max_signed_pod_values);

        // add the proofs of empty leaves (if needed), till the max_signed_pod_values
        let mut mp = MerkleClaimAndProof::empty();
        mp.root = input.dict.commitment();
        for i in curr..self.params.max_signed_pod_values {
            self.mt_proofs[i].set_targets(pw, false, &mp)?;
        }

        // get the signer pk
        // let pk = PublicKey(key_signer_value.raw()); // TODO WIP
        // the msg signed is the id
        // let msg = RawValue::from(input.id.0); // TODO uncomment

        // TODO uncomment
        // set signature targets values
        // pw.set_biguint_target(
        //     &self.msg.value,
        //     &biguint_from_array(std::array::from_fn(|i| msg.0[i].to_canonical_u64())),
        // )?;
        // pw.set_biguint_target(&self.pk.0.x.value, &biguint_from_array(input.pk.0.x.0))?;
        // pw.set_biguint_target(&self.pk.0.y.value, &biguint_from_array(input.pk.0.y.0))?;
        // pw.set_biguint_target(
        //     &self.signature.r.value,
        //     &biguint_from_array(input.signature.r.0),
        // )?;
        // pw.set_biguint_target(
        //     &self.signature.s.value,
        //     &biguint_from_array(input.signature.s.0),
        // )?;

        // set the id target value
        pw.set_hash_target(self.id, HashOut::from_vec(input.id.0 .0.to_vec()))?;

        pw.set_target_arr(&self.vds_root.elements, &input.vds_root.0)?;

        Ok(())
    }
}

impl EcdsaPodVerifyTarget {
    pub fn pub_statements(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        self_id: bool,
    ) -> Vec<StatementTarget> {
        let mut statements = Vec::new();
        let predicate =
            PredicateTarget::new_native(builder, &self.params, NativePredicate::ValueOf);
        let pod_id = if self_id {
            builder.constant_value(SELF.0.into())
        } else {
            ValueTarget {
                elements: self.id.elements,
            }
        };
        for mt_proof in &self.mt_proofs {
            let args = [
                StatementArgTarget::anchored_key(builder, &pod_id, &mt_proof.key),
                StatementArgTarget::literal(builder, &mt_proof.value),
            ]
            .into_iter()
            .chain(iter::repeat_with(|| StatementArgTarget::none(builder)))
            .take(self.params.max_statement_args)
            .collect();
            let statement = StatementTarget {
                predicate: predicate.clone(),
                args,
            };
            statements.push(statement);
        }
        statements
    }
}

use std::sync::{LazyLock, MappedRwLockReadGuard, RwLock, RwLockReadGuard};

use crate::timed;
static ECDSA_POD_DATA: LazyLock<
    RwLock<HashMap<Params, (EcdsaPodVerifyTarget, CircuitData<F, C, D>)>>,
> = LazyLock::new(|| RwLock::new(HashMap::new()));

/* TODO WIP build
/// build the circuit of EcdsaPodVerifyTarget, padded to the amount of gates
/// needed to make it compatible with the RecursiveCircuit
fn _build(params: &Params) -> Result<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> {
    let config = CircuitConfig::standard_recursion_config();
    // let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let ecdsapod_target = EcdsaPodVerifyTarget::build(&mut builder, params, &[] /*TODO*/)?;
    // let mainpod_circuit_data = crate::backends::plonky2::recursive_main_pod_circuit_data(params);
    let mainpod_circuit_data = recursive_main_pod_circuit_data_OPT(params);
    // crate::backends::plonky2::recursion::pad_circuit(&mut builder, &mainpod_circuit_data.common);

    let data = timed!("EcdsaPod build", builder.build::<C>());
    assert_eq!(mainpod_circuit_data.common, data.common);
    Ok((ecdsapod_target, data))
}
// fn build(params: &Params) -> (EcdsaPodVerifyTarget, CircuitData<F, C, D>) {
fn build(params: &Params) -> MappedRwLockReadGuard<(EcdsaPodVerifyTarget, CircuitData<F, C, D>)> {
    crate::backends::plonky2::get_or_set_map_cache(
        // &crate::backends::plonky2::RECURSIVE_MAIN_POD_DATA,
        &ECDSA_POD_DATA,
        params,
        |params| _build(params).expect("successful build"),
    )
}
*/

#[derive(Clone, Debug)]
pub struct EcdsaPod {
    params: Params,
    id: PodId,
    dict: Dictionary,
    proof: Proof,
    vds_hash: Hash,
    verifier_data: VerifierOnlyCircuitData<C, D>,
    // signature: ECDSASignature<Secp256K1>,
    // msg: F,
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
        kvs: &HashMap<Key, Value>,
        sk: ECDSASecretKey<Secp256K1>,
    ) -> Result<EcdsaPod> {
        // TODO use 'build'
        // let config = CircuitConfig::standard_recursion_config();
        // let rec_params = recursion::new_params::<MainPodVerifyTarget>(
        let rec_params = recursion::new_params::<EcdsaPodVerifyTarget>(
            params.max_input_recursive_pods,
            NUM_PUBLIC_INPUTS,
            params,
        )?;
        // let ecdsa_pod = RecursiveCircuit::<EcdsaPodVerifyTarget>::build(&rec_params, params)?;
        let config = CircuitConfig::standard_recursion_config();
        // let config = CircuitConfig::standard_ecc_config();
        // TODO rm next lines and replace it by the previous commented call `build`
        let mut builder = CircuitBuilder::new(config.clone());
        let targets = RecursiveCircuit::<EcdsaPodVerifyTarget>::build_targets(
            &mut builder,
            &rec_params,
            params,
        )?;
        // crate::backends::plonky2::recursion::pad_circuit(&mut builder, &rec_params.common_data);
        let prover: ProverCircuitData<F, C, D> = builder.build_prover::<C>();
        let ecdsa_pod = RecursiveCircuit::<EcdsaPodVerifyTarget> {
            params: rec_params.clone(),
            prover,
            target: targets,
        };

        // first sign the pod id
        let pubkey: ECDSAPublicKey<Secp256K1> =
            ECDSAPublicKey((CurveScalar(sk.0) * Secp256K1::GENERATOR_PROJECTIVE).to_affine());
        let mut kvs = kvs.clone();
        let pk_repr: Value = Value::from(EMPTY_VALUE); // TODO use full pk (eg. hash it)
        kvs.insert(Key::from(KEY_SIGNER), pk_repr);
        kvs.insert(Key::from(KEY_TYPE), Value::from(PodType::Signed));

        let dict = Dictionary::new(kvs)?;
        let id: PodId = PodId(dict.commitment());
        let id_raw = RawValue::from(id.0); // PodId as Value

        let id_u64: [u64; 4] = std::array::from_fn(|i| id_raw.0[i].to_canonical_u64());
        let msg: Secp256K1Scalar = Secp256K1Scalar(id_u64);
        let signature: ECDSASignature<Secp256K1> = sign_message(msg, sk);

        // now that sig is done, gen a plonky2 proof of the circuit that verifies it

        // TODO this will be done once at the beginning, not each time
        // let data = build(params)?;

        /*
        // build circuit targets
        // let config = CircuitConfig::standard_recursion_config();
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());
        dbg!("A 0");
        let ecdsa_targ = EcdsaPodVerifyTarget::build(&mut builder, params, &[] /*TODO*/)?;
        dbg!("A 1");

        // let circuit_data =
        //     // crate::backends::plonky2::circuits::mainpod::recursive_circuit_data(params)?;
        //     recursive_circuit_data_OPT(params, config)?;
        dbg!("A 2");
        // crate::backends::plonky2::emptypod::pad_circuit(&mut builder, &circuit_data.common);
        dbg!("A 3");
        */

        // set targets
        dbg!("A 4");
        let input = EcdsaPodVerifyInput {
            vds_root,
            id,
            // pk: pubkey, // TODO uncomment
            dict: dict.clone(),
            // signature,
        };
        let (dummy_verifier_data, dummy_proof) = dummy(
            &rec_params.common_data,
            NUM_PUBLIC_INPUTS, // TODO num_public_inputs,
        )?;
        let proof_with_pis = ecdsa_pod.prove(
            &input,
            // vec![], vec![]
            vec![dummy_proof.clone(), dummy_proof.clone()],
            vec![dummy_verifier_data.clone(), dummy_verifier_data.clone()],
        )?;
        // let mut pw = PartialWitness::<F>::new();
        // ecdsa_targ.set_targets(&mut pw, &input)?; //vds_root, id, pubkey, dict.clone(), signature)?;
        // dbg!("A 5");
        //
        // let data = builder.build::<C>();
        // dbg!("A 6");
        //
        // let proof = data.prove(pw)?;
        // dbg!("A 7");
        // let id = &proof.public_inputs[PI_OFFSET_ID..PI_OFFSET_ID + HASH_SIZE];
        // let id = PodId(Hash([id[0], id[1], id[2], id[3]]));

        #[cfg(test)] // sanity check
        rec_params.verifier_data().verify(proof_with_pis.clone())?;

        Ok(EcdsaPod {
            params: params.clone(),
            id,
            dict,
            proof: proof_with_pis.proof,
            vds_hash: EMPTY_HASH,
            verifier_data: rec_params.verifier_data().verifier_only.clone(),
            // TODO: rm 'verifier_data' field, and 'compute' it with the 'build'
            // method, so that the method 'EcdsaPod.verifier_data()' can get it
            // from there and not from an internal field
        })
    }
    fn new(
        params: &Params,
        vds_root: Hash,
        kvs: &HashMap<Key, Value>,
        sk: ECDSASecretKey<Secp256K1>,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        // TODO move _prove contents directly here, no need to abstract method
        Ok(Self::_prove(params, vds_root, kvs, sk).map(Box::new)?)
    }
    fn _verify(&self) -> Result<()> {
        dbg!("B 0");
        let mt = MerkleTree::new(
            MAX_DEPTH,
            &self
                .dict
                .kvs()
                .iter()
                .map(|(k, v)| (k.raw(), v.raw()))
                .collect::<HashMap<RawValue, RawValue>>(),
        )?;
        dbg!("B 1");
        let id = PodId(mt.root());
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        // TODO: cache these artefacts
        // let rec_params = recursion::new_params::<MainPodVerifyTarget>(
        let rec_params = recursion::new_params::<EcdsaPodVerifyTarget>(
            self.params.max_input_recursive_pods,
            NUM_PUBLIC_INPUTS,
            &self.params,
        )?;

        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(EMPTY_HASH.0.iter()) // slot for the unused vds root
            // .chain(self.vds_root.0.iter()) // TODO WIP
            .cloned()
            .collect_vec();

        dbg!("B 2");
        // let data = build(&self.params)?; // TODO don't build each time
        dbg!("B 3");
        // data.verify(ProofWithPublicInputs {
        rec_params
            .verifier_data()
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

    fn pub_self_statements(&self) -> Vec<Statement> {
        let id = self.id();
        // By convention we put the KEY_TYPE first and KEY_SIGNER second
        let mut kvs: HashMap<Key, Value> = self.dict.kvs().clone();
        let key_type = Key::from(KEY_TYPE);
        let value_type = kvs.remove(&key_type).expect("KEY_TYPE");
        let key_signer = Key::from(KEY_SIGNER);
        let value_signer = kvs.remove(&key_signer).expect("KEY_SIGNER");
        [(key_type, value_type), (key_signer, value_signer)]
            .into_iter()
            .chain(kvs.into_iter().sorted_by_key(|kv| kv.0.hash()))
            .map(|(k, v)| Statement::ValueOf(AnchoredKey::from((id, k)), v))
            .collect()
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

struct EcdsaPodVerifyCircuit {
    params: Params,
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

// use std::sync::{LazyLock, MappedRwLockReadGuard, RwLock, RwLockReadGuard};
// use crate::timed;
type CircuitData_OPT = CircuitData<F, C, D>;
static RECURSIVE_CIRCUIT_DATA: LazyLock<RwLock<HashMap<Params, CircuitData_OPT>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));
pub fn recursive_circuit_data_OPT(
    params: &Params,
    config: CircuitConfig,
) -> Result<MappedRwLockReadGuard<CircuitData_OPT>> {
    // Try to read from the hashmap with a readlock.  If the entry doesn't exist, acquire the write
    // lock, create and insert the entry and finally recurse to suceed with the read lock.
    {
        let read_lock = RECURSIVE_CIRCUIT_DATA.read().unwrap();
        if read_lock.get(params).is_some() {
            return Ok(RwLockReadGuard::map(read_lock, |m| m.get(params).unwrap()));
        }
    }
    {
        let mut write_lock = RECURSIVE_CIRCUIT_DATA.write().unwrap();
        if write_lock.get(params).is_none() {
            let data: CircuitData_OPT = timed!(
                "common_data_for_recursion",
                // common_data_for_recursion_OPT::<MainPodVerifyTarget>(
                common_data_for_recursion_OPT::<EcdsaPodVerifyTarget>(
                    config.clone(),
                    params.max_input_recursive_pods,
                    NUM_PUBLIC_INPUTS,
                    params
                )?
            );
            write_lock.insert(params.clone(), data);
        }
    }
    recursive_circuit_data_OPT(params, config.clone())
}
static RECURSIVE_MAIN_POD_DATA: LazyLock<RwLock<HashMap<Params, CircuitData<F, C, D>>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

pub fn recursive_main_pod_circuit_data_OPT(
    params: &Params,
) -> MappedRwLockReadGuard<CircuitData<F, C, D>> {
    crate::backends::plonky2::get_or_set_map_cache(&RECURSIVE_MAIN_POD_DATA, params, |params| {
        timed!(
            "common_data_for_recursion",
            common_data_for_recursion::<EcdsaPodVerifyTarget>(
                params.max_input_recursive_pods,
                NUM_PUBLIC_INPUTS,
                params
            )
            .expect("calculate common_data")
        )
    })
}

pub fn common_data_for_recursion_OPT<
    I: crate::backends::plonky2::recursion::circuit::InnerCircuit,
>(
    config: CircuitConfig,
    arity: usize,
    num_public_inputs: usize,
    inner_params: &I::Params,
) -> Result<CircuitData<F, C, D>> {
    // 1st
    // let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config.clone());
    let data = timed!("common_data_for_recursion 1st build", builder.build::<C>());

    // 2nd
    // let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    for _ in 0..arity {
        let verifier_data_i =
            builder.add_virtual_verifier_data(builder.config.fri_config.cap_height);

        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, &verifier_data_i, &data.common);
    }
    let data = timed!("common_data_for_recursion 2nd build", builder.build::<C>());

    // 3rd
    // let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());

    builder.add_gate_to_gate_set(plonky2::gates::gate::GateRef::new(
        plonky2::gates::constant::ConstantGate::new(config.num_constants),
    ));

    let verifier_datas_targ: Vec<plonky2::plonk::circuit_data::VerifierCircuitTarget> = (0..arity)
        .map(|_| builder.add_virtual_verifier_data(builder.config.fri_config.cap_height))
        .collect();
    for vd_i in verifier_datas_targ.iter() {
        let proof = builder.add_virtual_proof_with_pis(&data.common);
        builder.verify_proof::<C>(&proof, vd_i, &data.common);
    }

    // let prev_verifier_datas_hashes = builder.add_virtual_hashes(arity);
    // let vds_hash = gadget_hash_verifier_datas(
    //     &mut builder,
    //     arity,
    //     prev_verifier_datas_hashes.clone(),
    //     verifier_datas_targ.clone(),
    // );
    // // set vds_hash as public input
    // builder.register_public_inputs(&vds_hash.elements);

    // set the targets for the InnerCircuit
    let verified_proofs = (0..arity)
        .map(|_| {
            crate::backends::plonky2::recursion::circuit::VerifiedProofTarget::add_virtual(
                &mut builder,
                num_public_inputs,
            )
        })
        .collect_vec();
    let _ = timed!(
        "common_data_for_recursion I::build",
        I::build(&mut builder, inner_params, &verified_proofs)?
    );

    // pad min gates
    let n_gates = compute_num_gates(arity)?;
    while builder.num_gates() < n_gates {
        builder.add_gate(NoopGate, vec![]);
    }
    let circuit_data = timed!("common_data_for_recursion 3rd build", builder.build::<C>());
    // Make sure that the number of public inputs that the inner circuit has registered matches the
    // passed value.
    assert_eq!(num_public_inputs, circuit_data.common.num_public_inputs);
    Ok(circuit_data)
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
/*
*/

// TODO WIP, expose it from recurison::circuit.rs
use plonky2::{field::types::Field, plonk::circuit_data::VerifierOnlyCircuitData};
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
    crate::backends::plonky2::recursion::pad_circuit(&mut builder, common_data);

    let circuit_data = builder.build::<C>();

    let mut pw = PartialWitness::<F>::new();
    for target in &public_inputs {
        pw.set_target(*target, F::ZERO)?;
    }
    let proof = circuit_data.prove(pw)?;
    Ok((circuit_data.verifier_only, proof))
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
        // set max_signed_pod_values to 6, and we insert 3 leaves, so that the
        // circuit has enough space for the 3 leaves plus the KEY_TYPE and
        // KEY_SIGNER and one empty leaf.

        let mut kvs: HashMap<Key, Value> = HashMap::new();
        kvs.insert("idNumber".into(), "4242424242".into());
        kvs.insert("dateOfBirth".into(), 1169909384.into());
        kvs.insert("socialSecurityNumber".into(), "G2121210".into());

        let sk = ECDSASecretKey::<Secp256K1>(Secp256K1Scalar::rand());
        let vds_root = EMPTY_HASH;
        let ecdsa_pod = EcdsaPod::new(&params, vds_root, &kvs, sk).unwrap();
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
            crate::backends::plonky2::emptypod::EmptyPod::new(&params, EMPTY_HASH).unwrap();
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
