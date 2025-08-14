pub mod operation;
pub mod statement;
use std::{any::Any, iter, sync::Arc};

use itertools::Itertools;
pub use operation::*;
use plonky2::{hash::poseidon::PoseidonHash, plonk::config::Hasher};
use serde::{Deserialize, Serialize};
pub use statement::*;

use crate::{
    backends::plonky2::{
        basetypes::{CircuitData, Proof, ProofWithPublicInputs, VerifierOnlyCircuitData},
        cache::{self, CacheEntry},
        cache_get_standard_rec_main_pod_common_circuit_data,
        circuits::mainpod::{CustomPredicateVerification, MainPodVerifyInput, MainPodVerifyTarget},
        deserialize_proof, deserialize_verifier_only,
        emptypod::EmptyPod,
        error::{Error, Result},
        hash_common_data,
        mock::emptypod::MockEmptyPod,
        primitives::{
            ec::schnorr::SecretKey,
            merkletree::{MerkleClaimAndProof, MerkleTreeStateTransitionProof},
        },
        recursion::{
            hash_verifier_data, prove_rec_circuit, RecursiveCircuit, RecursiveCircuitTarget,
        },
        serialization::{
            CircuitDataSerializer, CommonCircuitDataSerializer, VerifierCircuitDataSerializer,
        },
        serialize_proof, serialize_verifier_only,
        signedpod::SignedPod,
    },
    middleware::{
        self, resolve_wildcard_values, value_from_op, AnchoredKey, CustomPredicateBatch,
        Error as MiddlewareError, Hash, MainPodInputs, NativeOperation, OperationType, Params, Pod,
        PodId, PodProver, PodType, RecursivePod, StatementArg, ToFields, VDSet, KEY_TYPE, SELF,
    },
    timed,
};

/// Hash a list of public statements to derive the PodId.  To make circuits with different number
/// of `max_public_statements compatible we pad the statements up to `num_public_statements_id`.
/// As an optimization we front pad with none-statements so that circuits with a small
/// `max_public_statements` only pay for `max_public_statements` by starting the poseidon state
/// with a precomputed constant corresponding to the front-padding part:
/// `id = hash(serialize(reverse(statements || none-statements)))`
pub fn calculate_id(statements: &[Statement], params: &Params) -> middleware::Hash {
    assert!(statements.len() <= params.num_public_statements_id);
    assert!(params.max_public_statements <= params.num_public_statements_id);

    let mut none_st: Statement = middleware::Statement::None.into();
    pad_statement(params, &mut none_st);
    let statements_back_padded = statements
        .iter()
        .chain(iter::repeat(&none_st))
        .take(params.num_public_statements_id)
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
    custom_predicate_batches: &[Arc<CustomPredicateBatch>],
) -> Result<Vec<CustomPredicateVerification>> {
    let mut table = Vec::new();
    for (i, op) in operations.iter().enumerate() {
        if let middleware::Operation::Custom(cpr, sts) = op {
            let wildcard_values =
                resolve_wildcard_values(params, cpr.predicate(), sts).expect("resolved wildcards");
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

    // Input signed pods region
    let dummy_signed_pod_box: Box<dyn Pod> = Box::new(SignedPod::dummy());
    let dummy_signed_pod = dummy_signed_pod_box.as_ref();
    assert!(inputs.signed_pods.len() <= params.max_input_signed_pods);
    for i in 0..params.max_input_signed_pods {
        let pod = inputs.signed_pods.get(i).unwrap_or(&dummy_signed_pod);
        let sts = pod.pub_statements();
        assert!(sts.len() <= params.max_signed_pod_values);
        for j in 0..params.max_signed_pod_values {
            let mut st = sts
                .get(j)
                .unwrap_or(&middleware::Statement::None)
                .clone()
                .into();
            pad_statement(params, &mut st);
            statements.push(st);
        }
    }

    // Input main pods region
    let empty_pod_box: Box<dyn RecursivePod> =
        if mock || inputs.recursive_pods.len() == params.max_input_recursive_pods {
            // We mocking or we don't need padding so we skip creating an EmptyPod
            MockEmptyPod::new_boxed(params, inputs.vd_set.clone())
        } else {
            EmptyPod::new_boxed(params, inputs.vd_set.clone())
        };
    let empty_pod = empty_pod_box.as_ref();
    assert!(inputs.recursive_pods.len() <= params.max_input_recursive_pods);
    for i in 0..params.max_input_recursive_pods {
        let pod = inputs.recursive_pods.get(i).copied().unwrap_or(empty_pod);
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
    assert!(inputs.public_statements.len() < params.max_public_statements);
    let pod_type = if mock {
        PodType::MockMain
    } else {
        PodType::Main
    };
    let mut type_st = middleware::Statement::Equal(
        AnchoredKey::from((SELF, KEY_TYPE)).into(),
        middleware::Value::from(pod_type).into(),
    )
    .into();
    pad_statement(params, &mut type_st);
    statements.push(type_st);

    for i in 0..(params.max_public_statements - 1) {
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
        [offset_public_statements..offset_public_statements + 1 + inputs.public_statements.len()]
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
    operations.push(Operation(
        OperationType::Native(NativeOperation::NewEntry),
        vec![],
        OperationAux::None,
    ));
    for i in 0..(params.max_public_statements - 1) {
        let st = &statements[offset_public_statements + i + 1];
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

impl PodProver for Prover {
    fn prove(
        &self,
        params: &Params,
        vd_set: &VDSet,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn RecursivePod>> {
        let signed_pods_input: Vec<SignedPod> = inputs
            .signed_pods
            .iter()
            .map(|p| {
                let p = (*p as &dyn Any)
                    .downcast_ref::<SignedPod>()
                    .expect("type SignedPod");
                p.clone()
            })
            .collect_vec();

        // Pad input recursive pods with empty pods if necessary
        let empty_pod = if inputs.recursive_pods.len() == params.max_input_recursive_pods {
            // We don't need padding so we skip creating an EmptyPod
            MockEmptyPod::new_boxed(params, inputs.vd_set.clone())
        } else {
            EmptyPod::new_boxed(params, inputs.vd_set.clone())
        };
        let inputs = MainPodInputs {
            recursive_pods: &inputs
                .recursive_pods
                .iter()
                .copied()
                .chain(iter::repeat(&*empty_pod))
                .take(params.max_input_recursive_pods)
                .collect_vec(),
            ..inputs
        };

        let recursive_pods_pub_self_statements = inputs
            .recursive_pods
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
            &custom_predicate_batches,
        )?;
        let public_key_of_sks =
            extract_public_key_of(params, &mut aux_list, inputs.operations, inputs.statements)?;

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
        let id: PodId = PodId(calculate_id(&public_statements, params));

        let common_hash: String = cache_get_rec_main_pod_common_hash(params).clone();
        let proofs = inputs
            .recursive_pods
            .iter()
            .map(|pod| {
                assert_eq!(pod.common_hash(), common_hash);
                assert_eq!(inputs.vd_set.root(), pod.vd_set().root());
                ProofWithPublicInputs {
                    proof: pod.proof(),
                    public_inputs: [pod.id().0 .0, inputs.vd_set.root().0].concat(),
                }
            })
            .collect_vec();
        let verifier_datas = inputs
            .recursive_pods
            .iter()
            .map(|pod| pod.verifier_data())
            .collect_vec();

        let vd_mt_proofs = vd_set.get_vds_proofs(&verifier_datas)?;

        let input = MainPodVerifyInput {
            vds_set: inputs.vd_set.clone(),
            vd_mt_proofs,
            signed_pods: signed_pods_input,
            recursive_pods_pub_self_statements,
            statements: statements[statements.len() - params.max_statements..].to_vec(),
            operations,
            merkle_proofs,
            public_key_of_sks,
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
            id,
            vd_set: inputs.vd_set,
            public_statements,
            proof: proof_with_pis.proof,
        }))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MainPod {
    params: Params,
    id: PodId,
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
            params.max_input_recursive_pods,
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
        let id = PodId(calculate_id(&self.public_statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
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
        let public_inputs = id
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

    fn id(&self) -> PodId {
        self.id
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

    fn serialize_data(&self) -> serde_json::Value {
        serde_json::to_value(Data {
            proof: serialize_proof(&self.proof),
            public_statements: self.public_statements.clone(),
            verifier_only: serialize_verifier_only(&self.verifier_only),
            common_hash: self.common_hash.clone(),
        })
        .expect("serialization to json")
    }
}

impl RecursivePod for MainPod {
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
    fn deserialize_data(
        params: Params,
        data: serde_json::Value,
        vd_set: VDSet,
        id: PodId,
    ) -> Result<Box<dyn RecursivePod>> {
        let data: Data = serde_json::from_value(data)?;
        let common = cache_get_rec_main_pod_common_circuit_data(&params);
        let proof = deserialize_proof(&common, &data.proof)?;
        let verifier_only = deserialize_verifier_only(&data.verifier_only)?;
        Ok(Box::new(Self {
            params,
            id,
            verifier_only,
            common_hash: data.common_hash,
            vd_set,
            proof,
            public_statements: data.public_statements,
        }))
    }
}

#[cfg(test)]
pub mod tests {
    use num::{BigUint, One};

    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::{MockMainPod, MockProver},
            primitives::ec::schnorr::SecretKey,
            signedpod::Signer,
        },
        examples::{
            attest_eth_friend, tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_sign_pod_builders,
            EthDosHelper,
        },
        frontend::{
            self, literal, CustomPredicateBatchBuilder, MainPodBuilder, StatementTmplBuilder as STB,
        },
        middleware::{
            self, containers::Set, CustomPredicateRef, NativePredicate as NP, DEFAULT_VD_LIST,
            DEFAULT_VD_SET,
        },
    };

    #[test]
    fn test_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_recursive_pods: 0,
            max_custom_predicate_batches: 0,
            max_custom_predicate_verifications: 0,
            ..Default::default()
        };
        println!("{:#?}", params);
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_pod_builders(&params);
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
            max_input_signed_pods: 1,
            max_input_recursive_pods: 1,
            max_signed_pod_values: 6,
            max_statements: 8,
            max_public_statements: 4,
            max_input_pods_public_statements: 10,
            ..Default::default()
        };
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let mut gov_id_builder = frontend::SignedPodBuilder::new(&params);
        gov_id_builder.insert("idNumber", "4242424242");
        gov_id_builder.insert("dateOfBirth", 1169909384);
        gov_id_builder.insert("socialSecurityNumber", "G2121210");
        let signer = Signer(SecretKey(42u64.into()));
        let gov_id = gov_id_builder.sign(&signer).unwrap();
        let now_minus_18y: i64 = 1169909388;
        let mut kyc_builder = frontend::MainPodBuilder::new(&params, &vd_set);
        kyc_builder.add_signed_pod(&gov_id);
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
            max_input_signed_pods: 0,
            max_input_recursive_pods: 0,
            max_signed_pod_values: 0,
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
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

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
            max_input_signed_pods: 0,
            max_input_recursive_pods: 0,
            max_input_pods_public_statements: 2,
            max_statements: 5,
            max_signed_pod_values: 2,
            max_public_statements: 2,
            num_public_statements_id: 4,
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
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

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

        let helper = EthDosHelper::new(&params, vd_set, false, alice.public_key())?;
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
            max_input_signed_pods: 0,
            max_input_recursive_pods: 0,
            max_statements: 9,
            max_public_statements: 4,
            max_statement_args: 4,
            max_operation_args: 4,
            max_custom_predicate_arity: 3,
            max_custom_batch_size: 3,
            max_custom_predicate_wildcards: 4,
            max_custom_predicate_verifications: 2,
            max_merkle_proofs_containers: 0,
            max_merkle_tree_state_transition_proofs_containers: 0,
            ..Default::default()
        };
        println!("{:#?}", params);
        let mut vds = DEFAULT_VD_LIST.clone();
        vds.push(rec_main_pod_circuit_data(&params).1.verifier_only.clone());
        let vd_set = VDSet::new(params.max_depth_mt_vds, &vds).unwrap();

        let mut cpb_builder = CustomPredicateBatchBuilder::new(params.clone(), "cpb".into());
        let stb0 = STB::new(NP::Equal).arg(("id", "score")).arg(literal(42));
        let stb1 = STB::new(NP::Equal)
            .arg(("secret_id", "key"))
            .arg(("id", "score"));
        let _ = cpb_builder.predicate_and(
            "pred_and",
            &["id"],
            &["secret_id"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = cpb_builder.predicate_or("pred_or", &["id"], &["secret_id"], &[stb0, stb1])?;
        let cpb = cpb_builder.finish();

        let cpb_and = CustomPredicateRef::new(cpb.clone(), 0);
        let _cpb_or = CustomPredicateRef::new(cpb.clone(), 1);

        let mut pod_builder = MainPodBuilder::new(&params, &vd_set);

        let st0 = pod_builder.priv_op(frontend::Operation::new_entry("score", 42))?;
        let st1 = pod_builder.priv_op(frontend::Operation::new_entry("key", 42))?;
        let st2 = pod_builder.priv_op(frontend::Operation::eq(st1.clone(), st0.clone()))?;

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
        let set = [1, 2, 3].into_iter().map(|n| n.into()).collect();
        let st = builder
            .pub_op(frontend::Operation::new_entry(
                "entry",
                Set::new(params.max_depth_mt_containers, set).unwrap(),
            ))
            .unwrap();

        builder.pub_op(frontend::Operation::set_contains(st, 1))?;

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
}
