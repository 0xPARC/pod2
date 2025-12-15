pub mod operation;
use crate::middleware::{wildcard_values_from_op_st, PodType};
pub mod statement;
use std::{iter, sync::Arc};

use itertools::{zip_eq, Itertools};
use num_bigint::BigUint;
pub use operation::*;
use plonky2::{hash::poseidon::PoseidonHash, plonk::config::Hasher};
use serde::{Deserialize, Serialize};
pub use statement::*;

use crate::{
    backends::plonky2::{
        basetypes::{CircuitData, Proof, ProofWithPublicInputs, VerifierOnlyCircuitData, F},
        cache::{self, CacheEntry},
        cache_get_standard_rec_main_pod_common_circuit_data,
        circuits::mainpod::{CustomPredicateVerification, MainPodVerifyInput, MainPodVerifyTarget},
        deserialize_proof, deserialize_verifier_only,
        emptypod::EmptyPod,
        error::{Error, Result},
        hash_common_data,
        mock::emptypod::MockEmptyPod,
        primitives::{
            ec::{
                curve::Point as PublicKey,
                schnorr::{SecretKey, Signature},
            },
            merkletree::{MerkleClaimAndProof, MerkleTreeStateTransitionProof},
        },
        recursion::{
            hash_verifier_data, prove_rec_circuit, RecursiveCircuit, RecursiveCircuitTarget,
        },
        serialization::{
            CircuitDataSerializer, CommonCircuitDataSerializer, VerifierCircuitDataSerializer,
        },
        serialize_proof, serialize_verifier_only,
    },
    middleware::{
        self, value_from_op, CustomPredicateBatch, Error as MiddlewareError, Hash, MainPodInputs,
        MainPodProver, NativeOperation, OperationType, Params, Pod, RawValue, StatementArg,
        ToFields, VDSet,
    },
    timed,
};

/// Hash a list of public statements to derive the Statements hash.  To make circuits with
/// different number of `max_public_statements compatible we pad the statements up to
/// `num_public_statements_id`. As an optimization we front pad with none-statements so that
/// circuits with a small `max_public_statements` only pay for `max_public_statements` by starting
/// the poseidon state with a precomputed constant corresponding to the front-padding part: `id =
/// hash(serialize(reverse(statements || none-statements)))`
pub fn calculate_statements_hash(statements: &[Statement], params: &Params) -> middleware::Hash {
    assert!(statements.len() <= params.num_public_statements_hash);
    assert!(params.max_public_statements <= params.num_public_statements_hash);

    let mut none_st: Statement = middleware::Statement::None.into();
    pad_statement(params, &mut none_st);
    let statements_back_padded = statements
        .iter()
        .chain(iter::repeat(&none_st))
        .take(params.num_public_statements_hash)
        .collect_vec();
    let field_elems = statements_back_padded
        .iter()
        .rev()
        .flat_map(|statement| statement.to_fields(params))
        .collect::<Vec<_>>();
    Hash(PoseidonHash::hash_no_pad(&field_elems).elements)
}

/// Extracts unique `CustomPredicateBatch`es from Custom ops.
pub(crate) fn extract_custom_predicate_batches(
    params: &Params,
    operations: &[middleware::Operation],
) -> Result<Vec<Arc<CustomPredicateBatch>>> {
    let custom_predicate_batches: Vec<_> = operations
        .iter()
        .flat_map(|op| match op {
            middleware::Operation::Custom(cpr, _) => Some(cpr.batch.clone()),
            _ => None,
        })
        .unique_by(|cpr| cpr.id())
        .collect();
    if custom_predicate_batches.len() > params.max_custom_predicate_batches {
        return Err(Error::custom(format!(
            "The number of required `CustomPredicateBatch`es ({}) exceeds the maximum number ({}).",
            custom_predicate_batches.len(),
            params.max_custom_predicate_batches
        )));
    }
    Ok(custom_predicate_batches)
}

/// Extracts all custom predicate operations with all the data required to verify them.
pub(crate) fn extract_custom_predicate_verifications(
    params: &Params,
    aux_list: &mut [OperationAux],
    operations: &[middleware::Operation],
    statements: &[middleware::Statement],
    custom_predicate_batches: &[Arc<CustomPredicateBatch>],
) -> Result<Vec<CustomPredicateVerification>> {
    let mut table = Vec::new();
    for (i, (op, st)) in zip_eq(operations.iter(), statements.iter()).enumerate() {
        if let middleware::Operation::Custom(cpr, sts) = op {
            if let middleware::Statement::Custom(st_cpr, st_args) = st {
                assert_eq!(cpr, st_cpr);
                let wildcard_values =
                    wildcard_values_from_op_st(params, cpr.predicate(), sts, st_args)
                        .expect("resolved wildcards");
                let sts = sts.iter().map(|s| Statement::from(s.clone())).collect();
                let batch_index = custom_predicate_batches
                    .iter()
                    .enumerate()
                    .find_map(|(i, cpb)| (cpb.id() == cpr.batch.id()).then_some(i))
                    .expect("find the custom predicate from the extracted unique list");
                let custom_predicate_table_index =
                    batch_index * params.max_custom_batch_size + cpr.index;
                aux_list[i] = OperationAux::CustomPredVerifyIndex(table.len());
                table.push(CustomPredicateVerification {
                    custom_predicate_table_index,
                    custom_predicate: cpr.clone(),
                    args: wildcard_values,
                    op_args: sts,
                });
            } else {
                panic!("Custom operation paired with non-custom statement");
            }
        }
    }

    if table.len() > params.max_custom_predicate_verifications {
        return Err(Error::custom(format!(
            "The number of required custom predicate verifications ({}) exceeds the maximum number ({}).",
            table.len(),
            params.max_custom_predicate_verifications
        )));
    }
    Ok(table)
}

/// Extracts Merkle proofs from Contains/NotContains ops.
pub(crate) fn extract_merkle_proofs(
    params: &Params,
    aux_list: &mut [OperationAux],
    operations: &[middleware::Operation],
    statements: &[middleware::Statement],
) -> Result<Vec<MerkleClaimAndProof>> {
    let mut table = Vec::new();
    for (i, (op, st)) in operations.iter().zip(statements.iter()).enumerate() {
        let deduction_err = || MiddlewareError::invalid_deduction(op.clone(), st.clone());
        let (root, key, value, pf) = match (op, st) {
            (
                middleware::Operation::ContainsFromEntries(root_s, key_s, value_s, pf),
                middleware::Statement::Contains(root_ref, key_ref, value_ref),
            ) => {
                let root = value_from_op(root_s, root_ref).ok_or_else(deduction_err)?;
                let key = value_from_op(key_s, key_ref).ok_or_else(deduction_err)?;
                let value = value_from_op(value_s, value_ref).ok_or_else(deduction_err)?;
                (root.raw(), key.raw(), Some(value.raw()), pf)
            }
            (
                middleware::Operation::NotContainsFromEntries(root_s, key_s, pf),
                middleware::Statement::NotContains(root_ref, key_ref),
            ) => {
                let root = value_from_op(root_s, root_ref).ok_or_else(deduction_err)?;
                let key = value_from_op(key_s, key_ref).ok_or_else(deduction_err)?;
                (root.raw(), key.raw(), None, pf)
            }
            _ => continue,
        };
        aux_list[i] = OperationAux::MerkleProofIndex(table.len());
        table.push(MerkleClaimAndProof::new(
            Hash::from(root),
            key,
            value,
            pf.clone(),
        ));
    }
    if table.len() > params.max_merkle_proofs_containers {
        return Err(Error::custom(format!(
            "The number of required Merkle proofs ({}) exceeds the maximum number ({}).",
            table.len(),
            params.max_merkle_proofs_containers
        )));
    }
    Ok(table)
}

/// Extracts Merkle state transition proofs from container update ops.
pub(crate) fn extract_merkle_tree_state_transition_proofs(
    params: &Params,
    aux_list: &mut [OperationAux],
    operations: &[middleware::Operation],
) -> Result<Vec<MerkleTreeStateTransitionProof>> {
    let mut table = Vec::new();
    for (i, op) in operations.iter().enumerate() {
        let pf = match op {
            middleware::Operation::ContainerInsertFromEntries(_, _, _, _, pf)
            | middleware::Operation::ContainerUpdateFromEntries(_, _, _, _, pf)
            | middleware::Operation::ContainerDeleteFromEntries(_, _, _, pf) => pf.clone(),
            _ => continue,
        };
        aux_list[i] = OperationAux::MerkleTreeStateTransitionProofIndex(table.len());
        table.push(pf);
    }
    if table.len() > params.max_merkle_tree_state_transition_proofs_containers {
        return Err(Error::custom(format!(
            "The number of required Merkle proofs ({}) exceeds the maximum number ({}).",
            table.len(),
            params.max_merkle_tree_state_transition_proofs_containers
        )));
    }
    Ok(table)
}

pub(crate) fn extract_public_key_of(
    params: &Params,
    aux_list: &mut [OperationAux],
    operations: &[middleware::Operation],
    statements: &[middleware::Statement],
) -> Result<Vec<SecretKey>> {
    let mut table = Vec::new();
    for (i, (op, st)) in operations.iter().zip(statements.iter()).enumerate() {
        if let (
            middleware::Operation::PublicKeyOf(_, sk_s),
            middleware::Statement::PublicKeyOf(_, sk_ref),
        ) = (op, st)
        {
            let deduction_err = || MiddlewareError::invalid_deduction(op.clone(), st.clone());
            let sk = SecretKey::try_from(
                value_from_op(sk_s, sk_ref)
                    .ok_or_else(deduction_err)?
                    .typed(),
            )?;
            aux_list[i] = OperationAux::PublicKeyOfIndex(table.len());
            table.push(sk);
        }
    }
    if table.len() > params.max_public_key_of {
        return Err(Error::custom(format!(
            "The number of required PublicKeyOf verifications ({}) exceeds the maximum number ({}).",
            table.len(),
            params.max_public_statements
        )));
    }
    Ok(table)
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SignedBy {
    pub msg: RawValue,
    pub pk: PublicKey,
    pub sig: Signature,
}

impl SignedBy {
    /// A valid deterministic signature from a known private key and nonce, used for padding
    pub fn dummy() -> Self {
        let sk = SecretKey(BigUint::from(1u32));
        let pk = sk.public_key();
        let msg = RawValue([F(0), F(0), F(0), F(0)]);
        let nonce = BigUint::from(2u32);
        let sig = sk.sign(msg, &nonce);
        Self { msg, pk, sig }
    }
}

/// Extracts Signatures verification data from SignedBy ops.
pub(crate) fn extract_signatures(
    params: &Params,
    aux_list: &mut [OperationAux],
    operations: &[middleware::Operation],
    statements: &[middleware::Statement],
) -> Result<Vec<SignedBy>> {
    let mut table = Vec::new();
    for (i, (op, st)) in operations.iter().zip(statements.iter()).enumerate() {
        let deduction_err = || MiddlewareError::invalid_deduction(op.clone(), st.clone());
        if let (
            middleware::Operation::SignedBy(msg_s, pk_s, sig),
            middleware::Statement::SignedBy(msg_ref, pk_ref),
        ) = (op, st)
        {
            let msg = value_from_op(msg_s, msg_ref).ok_or_else(deduction_err)?;
            let pk = value_from_op(pk_s, pk_ref).ok_or_else(deduction_err)?;
            aux_list[i] = OperationAux::SignedByIndex(table.len());
            table.push(SignedBy {
                msg: msg.raw(),
                pk: PublicKey::try_from(pk.typed())?,
                sig: sig.clone(),
            });
        }
    }
    if table.len() > params.max_signed_by {
        return Err(Error::custom(format!(
            "The number of required signatures ({}) exceeds the maximum number ({}).",
            table.len(),
            params.max_signed_by
        )));
    }
    Ok(table)
}

/// Find the operation argument statement in the list of previous statements and return the index.
fn find_op_arg(statements: &[Statement], op_arg: &middleware::Statement) -> Result<OperationArg> {
    // NOTE: The `None` `Statement` always exists as a constant at index 0
    statements
        .iter()
        .enumerate()
        .find_map(|(i, s)| {
            (&middleware::Statement::try_from(s.clone()).ok()? == op_arg).then_some(i)
        })
        .map(OperationArg::Index)
        .ok_or(Error::custom(format!(
            "Statement corresponding to op arg {} not found",
            op_arg
        )))
}

fn fill_pad<T: Clone>(v: &mut Vec<T>, pad_value: T, len: usize) {
    if v.len() > len {
        panic!("length exceeded");
    }
    while v.len() < len {
        v.push(pad_value.clone());
    }
}

pub fn pad_statement(params: &Params, s: &mut Statement) {
    fill_pad(&mut s.1, StatementArg::None, params.max_statement_args)
}

fn pad_operation_args(params: &Params, args: &mut Vec<OperationArg>) {
    fill_pad(args, OperationArg::None, params.max_operation_args)
}

/// Returns the statements from the given MainPodInputs, padding to the respective max lengths
/// defined at the given Params.  Also returns a copy of the dynamic-length public statements from
/// the list of statements.
pub(crate) fn layout_statements(
    params: &Params,
    mock: bool,
    inputs: &MainPodInputs,
) -> Result<(Vec<Statement>, Vec<Statement>)> {
    let mut statements = Vec::new();

    // Statement at index 0 is always None to be used for padding operation arguments in custom
    // predicate statements
    statements.push(middleware::Statement::None.into());

    // Input pods region
    let empty_pod_box: Box<dyn Pod> = if mock || inputs.pods.len() == params.max_input_pods {
        // We mocking or we don't need padding so we skip creating an EmptyPod
        MockEmptyPod::new_boxed(params, inputs.vd_set.clone())
    } else {
        EmptyPod::new_boxed(params, inputs.vd_set.clone())
    };
    let empty_pod = empty_pod_box.as_ref();
    assert!(inputs.pods.len() <= params.max_input_pods);
    for i in 0..params.max_input_pods {
        let pod = inputs.pods.get(i).copied().unwrap_or(empty_pod);
        let sts = pod.pub_statements();
        assert!(sts.len() <= params.max_public_statements);
        for j in 0..params.max_input_pods_public_statements {
            let mut st = sts
                .get(j)
                .unwrap_or(&middleware::Statement::None)
                .clone()
                .into();
            pad_statement(params, &mut st);
            statements.push(st);
        }
    }

    // Input statements
    assert!(
        inputs.statements.len() <= params.max_priv_statements(),
        "inputs.statements.len={} > params.max_priv_statements={}",
        inputs.statements.len(),
        params.max_priv_statements()
    );
    for i in 0..params.max_priv_statements() {
        let mut st = inputs
            .statements
            .get(i)
            .unwrap_or(&middleware::Statement::None)
            .clone()
            .into();
        pad_statement(params, &mut st);
        statements.push(st);
    }

    // Public statements
    assert!(inputs.public_statements.len() <= params.max_public_statements);
    for i in 0..params.max_public_statements {
        let mut st = inputs
            .public_statements
            .get(i)
            .unwrap_or(&middleware::Statement::None)
            .clone()
            .into();
        pad_statement(params, &mut st);
        statements.push(st);
    }

    let offset_public_statements = statements.len() - params.max_public_statements;
    let public_statements = statements
        [offset_public_statements..offset_public_statements + inputs.public_statements.len()]
        .to_vec();
    Ok((statements, public_statements))
}

pub(crate) fn process_private_statements_operations(
    params: &Params,
    statements: &[Statement],
    aux_list: &[OperationAux],
    input_operations: &[middleware::Operation],
) -> Result<Vec<Operation>> {
    assert_eq!(params.max_priv_statements(), aux_list.len());
    let mut operations = Vec::new();
    for (i, aux) in aux_list.iter().enumerate() {
        let op = input_operations
            .get(i)
            .unwrap_or(&middleware::Operation::None)
            .clone();
        let mid_args = op.args();
        let mut args = mid_args
            .iter()
            .map(|mid_arg| find_op_arg(statements, mid_arg))
            .collect::<Result<Vec<_>>>()?;

        pad_operation_args(params, &mut args);
        operations.push(Operation(op.op_type(), args, *aux));
    }
    Ok(operations)
}

// NOTE: In this implementation public statements are always copies from
// previous statements, so we fill in the operations accordingly.
/// This method assumes that the given `statements` array has been padded to
/// `params.max_statements`.
pub(crate) fn process_public_statements_operations(
    params: &Params,
    statements: &[Statement],
    mut operations: Vec<Operation>,
) -> Result<Vec<Operation>> {
    let offset_public_statements = statements.len() - params.max_public_statements;
    for st in statements.iter().skip(offset_public_statements) {
        let mut op = if st.is_none() {
            Operation(
                OperationType::Native(NativeOperation::None),
                vec![],
                OperationAux::None,
            )
        } else {
            let mid_arg = st.clone();
            Operation(
                OperationType::Native(NativeOperation::CopyStatement),
                vec![find_op_arg(statements, &mid_arg.try_into()?)?],
                OperationAux::None,
            )
        };
        fill_pad(&mut op.1, OperationArg::None, params.max_operation_args);
        operations.push(op);
    }
    Ok(operations)
}

pub struct Prover {}

impl MainPodProver for Prover {
    fn prove(&self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        // Pad input recursive pods with empty pods if necessary
        let empty_pod = if inputs.pods.len() == params.max_input_pods {
            // We don't need padding so we skip creating an EmptyPod
            MockEmptyPod::new_boxed(params, inputs.vd_set.clone())
        } else {
            EmptyPod::new_boxed(params, inputs.vd_set.clone())
        };
        let inputs = MainPodInputs {
            pods: &inputs
                .pods
                .iter()
                .copied()
                .chain(iter::repeat(&*empty_pod))
                .take(params.max_input_pods)
                .collect_vec(),
            ..inputs
        };

        let input_pods_pub_self_statements = inputs
            .pods
            .iter()
            .map(|pod| {
                assert_eq!(params.id_params(), pod.params().id_params());
                pod.pub_self_statements()
            })
            .collect_vec();

        // Aux values for backend::Operation
        let mut aux_list = vec![OperationAux::None; params.max_priv_statements()];
        let merkle_proofs =
            extract_merkle_proofs(params, &mut aux_list, inputs.operations, inputs.statements)?;
        let custom_predicate_batches = extract_custom_predicate_batches(params, inputs.operations)?;
        let custom_predicate_verifications = extract_custom_predicate_verifications(
            params,
            &mut aux_list,
            inputs.operations,
            inputs.statements,
            &custom_predicate_batches,
        )?;
        let public_key_of_sks =
            extract_public_key_of(params, &mut aux_list, inputs.operations, inputs.statements)?;
        let signed_bys =
            extract_signatures(params, &mut aux_list, inputs.operations, inputs.statements)?;

        let merkle_tree_state_transition_proofs =
            extract_merkle_tree_state_transition_proofs(params, &mut aux_list, inputs.operations)?;

        let (statements, public_statements) = layout_statements(params, false, &inputs)?;
        let operations = process_private_statements_operations(
            params,
            &statements,
            &aux_list,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        // get the id out of the public statements
        let sts_hash = calculate_statements_hash(&public_statements, params);

        let common_hash: String = cache_get_rec_main_pod_common_hash(params).clone();
        let proofs = inputs
            .pods
            .iter()
            .map(|pod| {
                assert_eq!(pod.common_hash(), common_hash);
                assert_eq!(inputs.vd_set.root(), pod.vd_set().root());
                ProofWithPublicInputs {
                    proof: pod.proof(),
                    public_inputs: [pod.statements_hash().0, inputs.vd_set.root().0].concat(),
                }
            })
            .collect_vec();
        let verifier_datas = inputs
            .pods
            .iter()
            .map(|pod| pod.verifier_data())
            .collect_vec();

        let mut vd_mt_proofs = Vec::with_capacity(inputs.pods.len());
        for (pod, vd) in inputs.pods.iter().zip(&verifier_datas) {
            vd_mt_proofs.push(if pod.is_main() {
                (true, inputs.vd_set.get_vds_proof(vd)?)
            } else {
                // For intro pods we don't verify inclusion of their vk into the vd set, so we
                // generate a dummy mt proof with expected root and value to pass some constraints
                (
                    false,
                    MerkleClaimAndProof {
                        root: inputs.vd_set.root(),
                        value: RawValue::from(pod.verifier_data_hash()),
                        ..MerkleClaimAndProof::empty()
                    },
                )
            });
        }

        let input = MainPodVerifyInput {
            vds_set: inputs.vd_set.clone(),
            vd_mt_proofs,
            input_pods_pub_self_statements,
            statements: statements[statements.len() - params.max_statements..].to_vec(),
            operations,
            merkle_proofs,
            public_key_of_sks,
            signed_bys,
            merkle_tree_state_transition_proofs,
            custom_predicate_batches,
            custom_predicate_verifications,
        };

        let (main_pod_target, circuit_data) = &*cache_get_rec_main_pod_circuit_data(params);
        let proof_with_pis = timed!(
            "MainPod::prove",
            prove_rec_circuit(
                main_pod_target,
                circuit_data,
                &input,
                proofs,
                verifier_datas
            )?
        );

        Ok(Box::new(MainPod {
            params: params.clone(),
            verifier_only: circuit_data.verifier_only.clone(),
            common_hash,
            sts_hash,
            vd_set: inputs.vd_set,
            public_statements,
            proof: proof_with_pis.proof,
        }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainPod {
    params: Params,
    sts_hash: Hash,
    verifier_only: VerifierOnlyCircuitData,
    common_hash: String,
    /// vds_root is the merkle-root of the `VDSet`, which contains the
    /// verifier_data hashes of the allowed set of VerifierOnlyCircuitData, for
    /// the succession of recursive MainPods, which when proving the POD, it is
    /// proven that all the recursive proofs that are being verified in-circuit
    /// use one of the verifier_data's contained in the VDSet.
    vd_set: VDSet,
    public_statements: Vec<Statement>,
    proof: Proof,
}

pub(crate) fn rec_main_pod_circuit_data(
    params: &Params,
) -> (RecursiveCircuitTarget<MainPodVerifyTarget>, CircuitData) {
    let rec_common_circuit_data = cache_get_standard_rec_main_pod_common_circuit_data();
    timed!(
        "recursive MainPod circuit_data padded",
        RecursiveCircuit::<MainPodVerifyTarget>::target_and_circuit_data_padded(
            params.max_input_pods,
            &rec_common_circuit_data,
            params,
        )
        .expect("calculate target_and_circuit_data_padded")
    )
}

pub(crate) fn cache_get_rec_main_pod_circuit_data(
    params: &Params,
) -> CacheEntry<(
    RecursiveCircuitTarget<MainPodVerifyTarget>,
    CircuitDataSerializer,
)> {
    // TODO(Edu): I believe that the standard_rec_main_pod_circuit data is the same as this when
    // the params are Default: we're padding the circuit to itself, so we get the original one?
    // If this is true we can deduplicate this cache entry because both rec_main_pod_circuit_data
    // and standard_rec_main_pod_circuit_data are indexed by Params.  This can be easily tested by
    // comparing the cached artifacts on disk :)
    cache::get("rec_main_pod_circuit_data", params, |params| {
        let (target, circuit_data) = rec_main_pod_circuit_data(params);
        (target, CircuitDataSerializer(circuit_data))
    })
    .expect("cache ok")
}

pub fn cache_get_rec_main_pod_verifier_circuit_data(
    params: &Params,
) -> CacheEntry<VerifierCircuitDataSerializer> {
    cache::get("rec_main_pod_verifier_circuit_data", params, |params| {
        let (_, rec_main_pod_circuit_data_padded) = &*cache_get_rec_main_pod_circuit_data(params);
        VerifierCircuitDataSerializer(rec_main_pod_circuit_data_padded.verifier_data().clone())
    })
    .expect("cache ok")
}

// This is a helper function to get the CommonCircuitData necessary to decode
// a serialized proof.
pub fn cache_get_rec_main_pod_common_circuit_data(
    params: &Params,
) -> CacheEntry<CommonCircuitDataSerializer> {
    cache::get("rec_main_pod_common_circuit_data", params, |params| {
        let (_, rec_main_pod_circuit_data_padded) = &*cache_get_rec_main_pod_circuit_data(params);
        CommonCircuitDataSerializer(rec_main_pod_circuit_data_padded.common.clone())
    })
    .expect("cache ok")
}

pub fn cache_get_rec_main_pod_common_hash(params: &Params) -> CacheEntry<String> {
    cache::get("rec_main_pod_common_hash", params, |params| {
        let common = &*cache_get_rec_main_pod_common_circuit_data(params);
        hash_common_data(common).expect("hash ok")
    })
    .expect("cache ok")
}

#[derive(Serialize, Deserialize)]
struct Data {
    public_statements: Vec<Statement>,
    proof: String,
    verifier_only: String,
    common_hash: String,
}

impl MainPod {
    pub fn proof(&self) -> Proof {
        self.proof.clone()
    }

    pub fn params(&self) -> &Params {
        &self.params
    }
}

impl Pod for MainPod {
    fn params(&self) -> &Params {
        &self.params
    }
    fn is_main(&self) -> bool {
        true
    }
    fn verify(&self) -> Result<()> {
        // 0. Assert that the CommonCircuitData of the pod is the current one
        let expect_common_hash = &*cache_get_rec_main_pod_common_hash(&self.params);
        if &self.common_hash != expect_common_hash {
            return Err(Error::custom(format!(
                "The pod common_hash: {} is different than the current one: {}",
                self.common_hash, expect_common_hash,
            )));
        }
        // 2. get the id out of the public statements
        let sts_hash = calculate_statements_hash(&self.public_statements, &self.params);
        if sts_hash != self.sts_hash {
            return Err(Error::statements_hash_not_equal(self.sts_hash, sts_hash));
        }

        // 7. verifier_data_hash is in the VDSet
        let verifier_data = self.verifier_data();
        let verifier_data_hash = hash_verifier_data(&verifier_data);
        if !self.vd_set.contains(verifier_data_hash) {
            return Err(Error::custom(format!(
                "vds_root in input recursive pod not in the set: {} not in {}",
                Hash(verifier_data_hash.elements),
                self.vd_set.root(),
            )));
        }

        // 1, 3, 4, 5 verification via the zkSNARK proof
        let rec_main_pod_verifier_circuit_data =
            &*cache_get_rec_main_pod_verifier_circuit_data(&self.params);
        let public_inputs = sts_hash
            .to_fields(&self.params)
            .iter()
            .chain(self.vd_set.root().0.iter())
            .cloned()
            .collect_vec();
        rec_main_pod_verifier_circuit_data
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::plonky2_proof_fail("MainPod", e))
    }

    fn statements_hash(&self) -> Hash {
        self.sts_hash
    }
    fn pod_type(&self) -> (usize, &'static str) {
        (PodType::Main as usize, "Main")
    }

    fn pub_self_statements(&self) -> Vec<middleware::Statement> {
        self.public_statements
            .iter()
            .cloned()
            .map(|st| st.try_into().expect("valid statement"))
            .collect()
    }

    fn verifier_data(&self) -> VerifierOnlyCircuitData {
        self.verifier_only.clone()
    }
    fn common_hash(&self) -> String {
        self.common_hash.clone()
    }
    fn proof(&self) -> Proof {
        self.proof.clone()
    }
    fn vd_set(&self) -> &VDSet {
        &self.vd_set
    }

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            public_statements: self.public_statements.clone(),
            verifier_only: serialize_verifier_only(&self.verifier_only),
            common_hash: self.common_hash.clone(),
        })
        .expect("serialization to json")
    }
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        sts_hash: Hash,
    ) -> Result<Self> {
        let data: Data = serde_json::from_value(data)?;
        let common = cache_get_rec_main_pod_common_circuit_data(&params);
        let proof = deserialize_proof(&common, &data.proof)?;
        let verifier_only = deserialize_verifier_only(&data.verifier_only)?;
        Ok(Self {
            params,
            sts_hash,
            verifier_only,
            common_hash: data.common_hash,
            vd_set,
            proof,
            public_statements: data.public_statements,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use std::{any::Any, collections::HashSet};

    use num::{BigUint, One};

    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::{MockMainPod, MockProver},
            primitives::ec::schnorr::SecretKey,
            signer::Signer,
        },
        dict,
        examples::{
            attest_eth_friend, tickets_pod_full_flow, zu_kyc_pod_builder,
            zu_kyc_sign_dict_builders, EthDosHelper,
        },
        frontend::{
            self, literal, CustomPredicateBatchBuilder, MainPodBuilder, StatementTmplBuilder as STB,
        },
        lang::parse,
        middleware::{
            self, containers::Set, CustomPredicateRef, NativePredicate as NP, Signer as _,
            DEFAULT_VD_LIST, DEFAULT_VD_SET,
        },
    };

    #[test]
    fn test_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_pods: 0,
            max_custom_predicate_batches: 0,
            max_custom_predicate_verifications: 0,
            ..Default::default()
        };
        println!("{:#?}", params);
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(&vds);

        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_dict_builders(&params);
        let signer = Signer(SecretKey(BigUint::one()));
        let gov_id_pod = gov_id_builder.sign(&signer)?;
        let signer = Signer(SecretKey(2u64.into()));
        let pay_stub_pod = pay_stub_builder.sign(&signer)?;
        let kyc_builder = zu_kyc_pod_builder(&params, &vd_set, &gov_id_pod, &pay_stub_pod)?;

        let prover = Prover {};
        let kyc_pod = kyc_builder.prove(&prover)?;
        crate::measure_gates_print!();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();

        Ok(pod.verify()?)
    }

    // `RUST_LOG=pod2::backends=debug cargo test --release --no-default-features --features=backend_plonky2,mem_cache,zk,metrics test_measure_main_pod -- --nocapture --ignored`
    #[ignore]
    #[test]
    fn test_measure_main_pod() -> frontend::Result<()> {
        env_logger::init();
        let params = Params::default();
        println!("{:#?}", params);
        let vd_set = VDSet::new(&[]);

        // Calculate rec common first to avoid duplicate metrics in `pod_builder.prove`
        let _rec_common_circuit_data = cache_get_standard_rec_main_pod_common_circuit_data();
        let pod_builder = MainPodBuilder::new(&params, &vd_set);
        let prover = Prover {};
        crate::measure_gates_reset!();
        let _pod = pod_builder.prove(&prover)?;
        crate::measure_gates_print!();
        Ok(())
    }

    #[test]
    fn test_main_tickets() -> frontend::Result<()> {
        let params = Params::default();

        let ticket_builder = tickets_pod_full_flow(&params, &DEFAULT_VD_SET)?;
        let prover = Prover {};
        let kyc_pod = ticket_builder.prove(&prover)?;
        crate::measure_gates_print!();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();

        Ok(pod.verify()?)
    }

    #[test]
    fn test_mini_0() {
        let params = middleware::Params {
            max_signed_by: 1,
            max_input_pods: 1,
            max_statements: 8,
            max_public_statements: 4,
            max_input_pods_public_statements: 10,
            ..Default::default()
        };
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(&vds);

        let mut gov_id_builder = frontend::SignedDictBuilder::new(&params);
        gov_id_builder.insert("idNumber", "4242424242");
        gov_id_builder.insert("dateOfBirth", 1169909384);
        gov_id_builder.insert("socialSecurityNumber", "G2121210");
        let signer = Signer(SecretKey(42u64.into()));
        let gov_id = gov_id_builder.sign(&signer).unwrap();
        let now_minus_18y: i64 = 1169909388;
        let mut kyc_builder = frontend::MainPodBuilder::new(&params, &vd_set);

        kyc_builder
            .priv_op(frontend::Operation::dict_signed_by(&gov_id))
            .unwrap();
        kyc_builder
            .pub_op(frontend::Operation::lt(
                (&gov_id, "dateOfBirth"),
                now_minus_18y,
            ))
            .unwrap();

        println!("{}", kyc_builder);
        println!();

        // Mock
        let prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&prover).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let prover = Prover {};
        let kyc_pod = kyc_builder.prove(&prover).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }

    // This pod does nothing but it's useful for debugging to keep things small.
    #[ignore]
    #[test]
    fn test_mini_1() {
        let params = middleware::Params {
            max_signed_by: 0,
            max_input_pods: 0,
            max_statements: 2,
            max_public_statements: 1,
            max_input_pods_public_statements: 0,
            max_merkle_proofs_containers: 0,
            max_public_key_of: 0,
            max_custom_predicate_verifications: 0,
            max_custom_predicate_batches: 0,
            ..Default::default()
        };
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(&vds);

        let builder = frontend::MainPodBuilder::new(&params, &vd_set);
        println!("{}", builder);
        println!();

        // Mock
        let prover = MockProver {};
        let pod = builder.prove(&prover).unwrap();
        let pod = (pod.pod as Box<dyn Any>).downcast::<MockMainPod>().unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let prover = Prover {};
        let pod = builder.prove(&prover).unwrap();
        let pod = (pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }

    #[test]
    fn test_mainpod_small_empty() {
        let params = middleware::Params {
            max_signed_by: 0,
            max_input_pods: 0,
            max_input_pods_public_statements: 2,
            max_statements: 5,
            max_public_statements: 2,
            num_public_statements_hash: 4,
            max_statement_args: 4,
            max_operation_args: 4,
            max_custom_predicate_batches: 2,
            max_custom_predicate_verifications: 2,
            max_custom_predicate_arity: 2,
            max_custom_predicate_wildcards: 3,
            max_custom_batch_size: 2,
            max_merkle_proofs_containers: 2,
            max_merkle_tree_state_transition_proofs_containers: 2,
            max_public_key_of: 2,
            max_depth_mt_containers: 4,
            max_depth_mt_vds: 6,
        };
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(&vds);

        let pod_builder = frontend::MainPodBuilder::new(&params, &vd_set);

        // Mock
        let prover = MockProver {};
        let kyc_pod = pod_builder.prove(&prover).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let prover = Prover {};
        let kyc_pod = pod_builder.prove(&prover).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }

    #[test]
    fn test_main_ethdos() -> frontend::Result<()> {
        let params = Params::default();
        println!("{:#?}", params);
        let vd_set = &*DEFAULT_VD_SET;

        let alice = Signer(SecretKey(1u32.into()));
        let bob = Signer(SecretKey(2u32.into()));
        let charlie = Signer(SecretKey(3u32.into()));

        // Alice attests that she is ETH friends with Bob and Bob
        // attests that he is ETH friends with Charlie.
        let alice_attestation = attest_eth_friend(&params, &alice, bob.public_key());
        let bob_attestation = attest_eth_friend(&params, &bob, charlie.public_key());

        let helper = EthDosHelper::new(&params, vd_set, alice.public_key())?;
        let prover = Prover {};
        let dist_1 = helper.dist_1(&alice_attestation)?.prove(&prover)?;
        crate::measure_gates_print!();
        dist_1.pod.verify()?;
        let dist_2 = helper
            .dist_n_plus_1(&dist_1, &bob_attestation)?
            .prove(&prover)?;
        Ok(dist_2.pod.verify()?)
    }

    #[test]
    fn test_main_mini_custom_1() -> frontend::Result<()> {
        let params = Params {
            max_signed_by: 0,
            max_input_pods: 0,
            max_statements: 9,
            max_public_statements: 4,
            max_statement_args: 4,
            max_operation_args: 4,
            max_custom_predicate_arity: 3,
            max_custom_batch_size: 3,
            max_custom_predicate_wildcards: 4,
            max_custom_predicate_verifications: 2,
            max_merkle_proofs_containers: 3,
            max_merkle_tree_state_transition_proofs_containers: 0,
            ..Default::default()
        };
        println!("{:#?}", params);
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(&vds);

        let mut cpb_builder = CustomPredicateBatchBuilder::new(params.clone(), "cpb".into());
        let stb0 = STB::new(NP::Contains)
            .arg("dict")
            .arg(literal("score"))
            .arg(literal(42));
        let stb1 = STB::new(NP::Equal)
            .arg(("secret_dict", "key"))
            .arg(("dict", "score"));
        let _ = cpb_builder.predicate_and(
            "pred_and",
            &["dict"],
            &["secret_dict"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = cpb_builder.predicate_or("pred_or", &["dict"], &["secret_dict"], &[stb0, stb1])?;
        let cpb = cpb_builder.finish();

        let cpb_and = CustomPredicateRef::new(cpb.clone(), 0);
        let _cpb_or = CustomPredicateRef::new(cpb.clone(), 1);

        let mut pod_builder = MainPodBuilder::new(&params, &vd_set);

        let dict = dict!({"score" => 42});
        let secret_dict = dict!({"key" => 42});
        let st0 = pod_builder.priv_op(frontend::Operation::dict_contains(
            dict.clone(),
            "score",
            42,
        ))?;
        let st2 = pod_builder.priv_op(frontend::Operation::eq(
            (&secret_dict.clone(), "key"),
            (&dict, "score"),
        ))?;

        let _st3 = pod_builder.priv_op(frontend::Operation::custom(cpb_and.clone(), [st0, st2]))?;

        let prover = MockProver {};
        let pod = pod_builder.prove(&prover)?;
        assert!(pod.pod.verify().is_ok());

        let prover = Prover {};
        let pod = pod_builder.prove(&prover)?;
        crate::measure_gates_print!();

        let pod = (pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();

        Ok(pod.verify()?)
    }

    #[test]
    fn test_set_contains() -> frontend::Result<()> {
        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params, &DEFAULT_VD_SET);
        let set: HashSet<_> = [1, 2, 3].into_iter().map(|n| n.into()).collect();
        let set = Set::new(set);
        builder.pub_op(frontend::Operation::set_contains(set, 1))?;

        let prover = Prover {};
        let proof = builder.prove(&prover).unwrap();
        let pod = (proof.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        Ok(pod.verify()?)
    }

    #[test]
    fn test_common() {
        use pretty_assertions::assert_eq;
        let params = Params::default();
        let main_common = &*cache_get_rec_main_pod_common_circuit_data(&params);
        let std_common = &*cache_get_standard_rec_main_pod_common_circuit_data();
        assert_eq!(std_common.0, main_common.0);
    }

    #[test]
    fn test_negative_less_than_zero() -> frontend::Result<()> {
        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params, &DEFAULT_VD_SET);
        builder.pub_op(frontend::Operation::lt(-1, 0))?;
        let prover = Prover {};
        builder.prove(&prover)?;
        Ok(())
    }

    #[test]
    fn test_undetermined_values() {
        let params = Default::default();
        let batch = parse(
            r#"
            two_equal(x,y,z) = OR(
                Equal(x,y)
                Equal(y,z)
                Equal(x,z)
            )
            "#,
            &params,
            &[],
        )
        .unwrap()
        .custom_batch;
        let mut builder = MainPodBuilder::new(&params, &DEFAULT_VD_SET);
        let cpr = CustomPredicateRef { batch, index: 0 };
        let eq_st = builder.priv_op(frontend::Operation::eq(1, 1)).unwrap();
        let op = frontend::Operation::custom(
            cpr.clone(),
            [
                eq_st,
                middleware::Statement::None,
                middleware::Statement::None,
            ],
        );
        let st = middleware::Statement::Custom(
            cpr,
            [1, 1, 2].into_iter().map(middleware::Value::from).collect(),
        );
        builder.insert(true, (st, op)).unwrap();
        let prover = Prover {};
        builder.prove(&prover).unwrap();
    }
}
