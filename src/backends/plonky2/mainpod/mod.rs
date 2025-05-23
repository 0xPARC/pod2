pub mod operation;
pub mod statement;
use std::{any::Any, iter, sync::Arc};

use base64::{prelude::BASE64_STANDARD, Engine};
use itertools::Itertools;
pub use operation::*;
use plonky2::{
    hash::poseidon::PoseidonHash,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData, ProverCircuitData},
        config::Hasher,
        proof::{Proof, ProofWithPublicInputs},
    },
    util::serialization::{Buffer, Read},
};
pub use statement::*;

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        circuits::mainpod::{
            CustomPredicateVerification, MainPodVerifyCircuit, MainPodVerifyInput,
            MainPodVerifyTarget, NUM_PUBLIC_INPUTS,
        },
        error::{Error, Result},
        primitives::merkletree::MerkleClaimAndProof,
        recursion::{self, RecursiveCircuit},
        signedpod::SignedPod,
    },
    middleware::{
        self, resolve_wildcard_values, AnchoredKey, CustomPredicateBatch, DynError, Hash,
        MainPodInputs, NativeOperation, NonePod, OperationType, Params, Pod, PodId, PodProver,
        PodType, StatementArg, ToFields, EMPTY_HASH, F, KEY_TYPE, SELF,
    },
};

/// Hash a list of public statements to derive the PodId.  To make circuits with different number
/// of `max_public_statements compatible we pad the statements up to `num_public_statements_id`.
/// As an optimization we front pad with none-statements so that circuits with a small
/// `max_public_statements` only pay for `max_public_statements` by starting the poseidon state
/// with a precomputed constant corresponding to the front-padding part:
/// `id = hash(serialize(reverse(statements || none-statements)))`
pub(crate) fn calculate_id(statements: &[Statement], params: &Params) -> middleware::Hash {
    assert_eq!(params.max_public_statements, statements.len());
    assert!(params.max_public_statements <= params.num_public_statements_id);
    statements
        .iter()
        .for_each(|st| assert_eq!(params.max_statement_args, st.1.len()));

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
    operations: &[middleware::Operation],
    custom_predicate_batches: &[Arc<CustomPredicateBatch>],
) -> Result<Vec<CustomPredicateVerification>> {
    let custom_predicate_data: Vec<_> = operations
        .iter()
        .flat_map(|op| match op {
            middleware::Operation::Custom(cpr, sts) => Some((cpr, sts)),
            _ => None,
        })
        .map(|(cpr, sts)| {
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
            CustomPredicateVerification {
                custom_predicate_table_index,
                custom_predicate: cpr.clone(),
                args: wildcard_values,
                op_args: sts,
            }
        })
        .collect();
    if custom_predicate_data.len() > params.max_custom_predicate_verifications {
        return Err(Error::custom(format!(
            "The number of required custom predicate verifications ({}) exceeds the maximum number ({}).",
            custom_predicate_data.len(),
            params.max_custom_predicate_verifications
        )));
    }
    Ok(custom_predicate_data)
}

/// Extracts Merkle proofs from Contains/NotContains ops.
pub(crate) fn extract_merkle_proofs(
    params: &Params,
    operations: &[middleware::Operation],
) -> Result<Vec<MerkleClaimAndProof>> {
    let merkle_proofs: Vec<_> = operations
        .iter()
        .flat_map(|op| match op {
            middleware::Operation::ContainsFromEntries(
                middleware::Statement::ValueOf(_, root),
                middleware::Statement::ValueOf(_, key),
                middleware::Statement::ValueOf(_, value),
                pf,
            ) => Some(MerkleClaimAndProof::new(
                Hash::from(root.raw()),
                key.raw(),
                Some(value.raw()),
                pf.clone(),
            )),
            middleware::Operation::NotContainsFromEntries(
                middleware::Statement::ValueOf(_, root),
                middleware::Statement::ValueOf(_, key),
                pf,
            ) => Some(MerkleClaimAndProof::new(
                Hash::from(root.raw()),
                key.raw(),
                None,
                pf.clone(),
            )),
            _ => None,
        })
        .collect();
    if merkle_proofs.len() > params.max_merkle_proofs {
        return Err(Error::custom(format!(
            "The number of required Merkle proofs ({}) exceeds the maximum number ({}).",
            merkle_proofs.len(),
            params.max_merkle_proofs
        )));
    }
    Ok(merkle_proofs)
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

/// Find the operation auxiliary data in the list of auxiliary data and return the index.
// NOTE: The `custom_predicate_verifications` is optional because in the MainPod we want to store
// the index of a custom predicate verification in the aux data, but in the MockMainPod we don't
// need that because we keep a reference to the custom predicate in the operation type, which
// removes the need for indexing.  We could change the OperationType and Predicate for the backend
// to not keep a reference to the custom predicate and instead just keep the id and index and then
// do the same double indexing that the MainPod does to verify custom predicates.
fn find_op_aux(
    merkle_proofs: &[MerkleClaimAndProof],
    custom_predicate_verifications: Option<&[CustomPredicateVerification]>,
    op: &middleware::Operation,
) -> Result<OperationAux> {
    let op_aux = op.aux();
    if let (middleware::Operation::Custom(cpr, op_args), Some(cpvs)) =
        (op, custom_predicate_verifications)
    {
        return Ok(cpvs
            .iter()
            .enumerate()
            .find_map(|(i, cpv)| {
                (cpv.custom_predicate.batch.id() == cpr.batch.id()
                    && cpv.custom_predicate.index == cpr.index
                    && cpv
                        .op_args
                        .iter()
                        .zip_eq(op_args.iter())
                        .all(|(a0, a1)| a0.0 == a1.predicate() && a0.1 == a1.args()))
                .then_some(i)
            })
            .map(OperationAux::CustomPredVerifyIndex)
            .expect("custom predicate verification in the list"));
    }
    match &op_aux {
        middleware::OperationAux::None => Ok(OperationAux::None),
        middleware::OperationAux::MerkleProof(pf_arg) => merkle_proofs
            .iter()
            .enumerate()
            .find_map(|(i, pf)| (pf.proof == *pf_arg).then_some(i))
            .map(OperationAux::MerkleProofIndex)
            .ok_or(Error::custom(format!(
                "Merkle proof corresponding to op arg {} not found",
                op_aux
            ))),
    }
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

/// Returns the statements from the given MainPodInputs, padding to the
/// respective max lengths defined at the given Params.
pub(crate) fn layout_statements(params: &Params, inputs: &MainPodInputs) -> Vec<Statement> {
    let mut statements = Vec::new();

    // Statement at index 0 is always None to be used for padding operation arguments in custom
    // predicate statements
    statements.push(middleware::Statement::None.into());

    // Input signed pods region
    let none_sig_pod_box: Box<dyn Pod> = Box::new(NonePod {});
    let none_sig_pod = none_sig_pod_box.as_ref();
    assert!(inputs.signed_pods.len() <= params.max_input_signed_pods);
    for i in 0..params.max_input_signed_pods {
        let pod = inputs.signed_pods.get(i).unwrap_or(&none_sig_pod);
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
    let none_main_pod_box: Box<dyn Pod> = Box::new(NonePod {});
    let none_main_pod = none_main_pod_box.as_ref();
    assert!(inputs.main_pods.len() <= params.max_input_main_pods);
    for i in 0..params.max_input_main_pods {
        let pod = inputs.main_pods.get(i).copied().unwrap_or(none_main_pod);
        let sts = pod.pub_statements();
        assert!(sts.len() <= params.max_public_statements);
        for j in 0..params.max_public_statements {
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
    assert!(inputs.statements.len() <= params.max_priv_statements());
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
    let mut type_st = middleware::Statement::ValueOf(
        AnchoredKey::from((SELF, KEY_TYPE)),
        middleware::Value::from(PodType::MockMain),
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

    statements
}

pub(crate) fn process_private_statements_operations(
    params: &Params,
    statements: &[Statement],
    merkle_proofs: &[MerkleClaimAndProof],
    custom_predicate_verifications: Option<&[CustomPredicateVerification]>,
    input_operations: &[middleware::Operation],
) -> Result<Vec<Operation>> {
    let mut operations = Vec::new();
    for i in 0..params.max_priv_statements() {
        let op = input_operations
            .get(i)
            .unwrap_or(&middleware::Operation::None)
            .clone();
        let mid_args = op.args();
        let mut args = mid_args
            .iter()
            .map(|mid_arg| find_op_arg(statements, mid_arg))
            .collect::<Result<Vec<_>>>()?;

        let aux = find_op_aux(merkle_proofs, custom_predicate_verifications, &op)?;

        pad_operation_args(params, &mut args);
        operations.push(Operation(op.op_type(), args, aux));
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

impl Prover {
    fn _prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<MainPod> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        // TODO: Cache this somehow
        let rec_params = recursion::new_params::<MainPodVerifyTarget>(
            params.max_input_main_pods,
            NUM_PUBLIC_INPUTS,
            params,
        )?;
        let main_pod_target = RecursiveCircuit::<MainPodVerifyTarget>::build_targets(
            &mut builder,
            &rec_params,
            params,
        )?;
        let prover: ProverCircuitData<F, C, D> = builder.build_prover::<C>();
        let main_pod = RecursiveCircuit {
            params: rec_params,
            prover,
            target: main_pod_target,
        };

        let mut pw = PartialWitness::<F>::new();
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

        let main_pods_input: Vec<MainPod> = inputs
            .main_pods
            .iter()
            .map(|p| {
                let p = (*p as &dyn Any)
                    .downcast_ref::<MainPod>()
                    .expect("type MainPod");
                p.clone()
            })
            .collect_vec();

        let merkle_proofs = extract_merkle_proofs(params, inputs.operations)?;
        let custom_predicate_batches = extract_custom_predicate_batches(params, inputs.operations)?;
        let custom_predicate_verifications = extract_custom_predicate_verifications(
            params,
            inputs.operations,
            &custom_predicate_batches,
        )?;

        let statements = layout_statements(params, &inputs);
        let operations = process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            Some(&custom_predicate_verifications),
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();
        // get the id out of the public statements
        let id: PodId = PodId(calculate_id(&public_statements, params));

        let input = MainPodVerifyInput {
            vds_root: inputs.vds_root,
            signed_pods: signed_pods_input,
            main_pods: main_pods_input,
            statements: statements[statements.len() - params.max_statements..].to_vec(),
            operations,
            merkle_proofs,
            custom_predicate_batches,
            custom_predicate_verifications,
        };
        let proofs = todo!();
        let verifier_datas = todo!();
        let proof_with_pis = main_pod.prove(&input, proofs, verifier_datas)?;

        Ok(MainPod {
            params: params.clone(),
            id,
            vds_root: inputs.vds_root,
            public_statements,
            proof: proof_with_pis.proof,
        })
    }
}

impl PodProver for Prover {
    fn prove(
        &mut self,
        params: &Params,
        inputs: MainPodInputs,
    ) -> Result<Box<dyn Pod>, Box<DynError>> {
        Ok(self._prove(params, inputs).map(Box::new)?)
    }
}

pub type MainPodProof = Proof<F, C, D>;

#[derive(Clone, Debug)]
pub struct MainPod {
    params: Params,
    id: PodId,
    vds_root: Hash,
    public_statements: Vec<Statement>,
    proof: MainPodProof,
}

/// Convert a Statement into middleware::Statement and replace references to SELF by `self_id`.
pub(crate) fn normalize_statement(statement: &Statement, self_id: PodId) -> middleware::Statement {
    Statement(
        statement.0.clone(),
        statement
            .1
            .iter()
            .map(|sa| match &sa {
                StatementArg::Key(AnchoredKey { pod_id, key }) if *pod_id == SELF => {
                    StatementArg::Key(AnchoredKey::new(self_id, key.clone()))
                }
                _ => sa.clone(),
            })
            .collect(),
    )
    .try_into()
    .unwrap()
}

// This is a helper function to get the CommonCircuitData necessary to decode
// a serialized proof. At some point in the future, this data may be available
// as a constant or with static initialization, but in the meantime we can
// generate it on-demand.
fn get_common_data(params: &Params) -> Result<CommonCircuitData<F, D>, Error> {
    // TODO: Cache this somehow
    let rec_params = recursion::new_params::<MainPodVerifyTarget>(
        params.max_input_main_pods,
        NUM_PUBLIC_INPUTS,
        params,
    )?;
    Ok(rec_params.common_data().clone())
}

impl MainPod {
    fn _verify(&self) -> Result<()> {
        // 2. get the id out of the public statements
        let id = PodId(calculate_id(&self.public_statements, &self.params));
        if id != self.id {
            return Err(Error::id_not_equal(self.id, id));
        }

        // 1, 3, 4, 5 verification via the zkSNARK proof
        // TODO: cache these artefacts
        let rec_params = recursion::new_params::<MainPodVerifyTarget>(
            self.params.max_input_main_pods,
            NUM_PUBLIC_INPUTS,
            &self.params,
        )?;
        let public_inputs = id
            .to_fields(&self.params)
            .iter()
            .chain(self.vds_root.0.iter())
            .cloned()
            .collect_vec();
        rec_params
            .verifier_data()
            .verify(ProofWithPublicInputs {
                proof: self.proof.clone(),
                public_inputs,
            })
            .map_err(|e| Error::custom(format!("MainPod proof verification failure: {:?}", e)))
    }

    pub fn proof(&self) -> MainPodProof {
        self.proof.clone()
    }

    pub fn vds_root(&self) -> Hash {
        self.vds_root
    }

    pub fn params(&self) -> &Params {
        &self.params
    }

    pub(crate) fn new(
        proof: MainPodProof,
        public_statements: Vec<Statement>,
        id: PodId,
        vds_root: Hash,
        params: Params,
    ) -> Self {
        Self {
            params,
            id,
            vds_root,
            public_statements,
            proof,
        }
    }

    pub fn decode_proof(proof: &str, params: &Params) -> Result<MainPodProof, Error> {
        let decoded = BASE64_STANDARD.decode(proof).map_err(|e| {
            Error::custom(format!(
                "Failed to decode proof from base64: {}. Value: {}",
                e, proof
            ))
        })?;
        let mut buf = Buffer::new(&decoded);
        let common = get_common_data(params)?;

        let proof = buf.read_proof(&common).map_err(|e| {
            Error::custom(format!(
                "Failed to read proof from buffer: {}. Value: {}",
                e, proof
            ))
        })?;

        Ok(proof)
    }
}

impl Pod for MainPod {
    fn verify(&self) -> Result<(), Box<DynError>> {
        Ok(self._verify()?)
    }

    fn id(&self) -> PodId {
        self.id
    }

    fn pub_statements(&self) -> Vec<middleware::Statement> {
        // return the public statements, where when origin=SELF is replaced by origin=self.id()
        self.public_statements
            .iter()
            .cloned()
            .map(|statement| normalize_statement(&statement, self.id()))
            .collect()
    }

    fn serialized_proof(&self) -> String {
        let mut buffer = Vec::new();
        use plonky2::util::serialization::Write;
        buffer.write_proof(&self.proof).unwrap();
        BASE64_STANDARD.encode(buffer)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::{MockMainPod, MockProver},
            primitives::signature::SecretKey,
            signedpod::Signer,
        },
        examples::{
            eth_dos_pod_builder, eth_friend_signed_pod_builder, zu_kyc_pod_builder,
            zu_kyc_sign_pod_builders,
        },
        frontend::{
            key, literal, CustomPredicateBatchBuilder, MainPodBuilder, StatementTmplBuilder as STB,
            {self},
        },
        middleware,
        middleware::{CustomPredicateRef, NativePredicate as NP, RawValue},
        op,
    };

    #[test]
    fn test_main_zu_kyc() -> frontend::Result<()> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_main_pods: 0,
            max_custom_predicate_batches: 0,
            max_custom_predicate_verifications: 0,
            ..Default::default()
        };
        println!("{:#?}", params);

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params);
        let mut signer = Signer(SecretKey(RawValue::from(1)));
        let gov_id_pod = gov_id_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(2)));
        let pay_stub_pod = pay_stub_builder.sign(&mut signer)?;
        let mut signer = Signer(SecretKey(RawValue::from(3)));
        let sanction_list_pod = sanction_list_builder.sign(&mut signer)?;
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod)?;

        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;
        crate::measure_gates_print!();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();

        Ok(pod.verify()?)
    }

    #[test]
    fn test_mini_0() {
        let params = middleware::Params {
            max_input_signed_pods: 1,
            max_input_main_pods: 1,
            max_signed_pod_values: 6,
            max_statements: 8,
            max_public_statements: 4,
            ..Default::default()
        };

        let mut gov_id_builder = frontend::SignedPodBuilder::new(&params);
        gov_id_builder.insert("idNumber", "4242424242");
        gov_id_builder.insert("dateOfBirth", 1169909384);
        gov_id_builder.insert("socialSecurityNumber", "G2121210");
        let mut signer = Signer(SecretKey(RawValue::from(42)));
        let gov_id = gov_id_builder.sign(&mut signer).unwrap();
        let now_minus_18y: i64 = 1169909388;
        let mut kyc_builder = frontend::MainPodBuilder::new(&params);
        kyc_builder.add_signed_pod(&gov_id);
        kyc_builder
            .pub_op(op!(lt, (&gov_id, "dateOfBirth"), now_minus_18y))
            .unwrap();

        println!("{}", kyc_builder);
        println!();

        // Mock
        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }

    #[test]
    fn test_mainpod_small_empty() {
        let params = middleware::Params {
            max_input_signed_pods: 0,
            max_input_main_pods: 0,
            max_input_pods_public_statements: 2,
            max_statements: 5,
            max_signed_pod_values: 2,
            max_public_statements: 2,
            num_public_statements_id: 4,
            max_statement_args: 2,
            max_operation_args: 3,
            max_custom_predicate_batches: 2,
            max_custom_predicate_verifications: 2,
            max_custom_predicate_arity: 2,
            max_custom_predicate_wildcards: 2,
            max_custom_batch_size: 2,
            max_merkle_proofs: 2,
            max_depth_mt_gadget: 4,
        };

        let pod_builder = frontend::MainPodBuilder::new(&params);

        // Mock
        let mut prover = MockProver {};
        let kyc_pod = pod_builder.prove(&mut prover, &params).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>)
            .downcast::<MockMainPod>()
            .unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let mut prover = Prover {};
        let kyc_pod = pod_builder.prove(&mut prover, &params).unwrap();
        let pod = (kyc_pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }

    #[test]
    fn test_main_ethdos() -> frontend::Result<()> {
        let params = Params {
            max_input_signed_pods: 2,
            max_input_main_pods: 1,
            max_statements: 26,
            max_public_statements: 5,
            max_signed_pod_values: 8,
            max_statement_args: 6,
            max_operation_args: 4,
            max_custom_predicate_arity: 4,
            max_custom_batch_size: 3,
            max_custom_predicate_wildcards: 12,
            max_custom_predicate_verifications: 8,
            ..Default::default()
        };
        println!("{:#?}", params);

        let mut alice = Signer(SecretKey(RawValue::from(1)));
        let bob = Signer(SecretKey(RawValue::from(2)));
        let mut charlie = Signer(SecretKey(RawValue::from(3)));

        // Alice attests that she is ETH friends with Charlie and Charlie
        // attests that he is ETH friends with Bob.
        let alice_attestation =
            eth_friend_signed_pod_builder(&params, charlie.public_key().0.into())
                .sign(&mut alice)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.public_key().0.into()).sign(&mut charlie)?;

        let alice_bob_ethdos_builder = eth_dos_pod_builder(
            &params,
            false,
            &alice_attestation,
            &charlie_attestation,
            bob.public_key().0.into(),
        )?;

        let mut prover = MockProver {};
        let pod = alice_bob_ethdos_builder.prove(&mut prover, &params)?;
        assert!(pod.pod.verify().is_ok());

        let mut prover = Prover {};
        let alice_bob_ethdos = alice_bob_ethdos_builder.prove(&mut prover, &params)?;
        crate::measure_gates_print!();
        let pod = (alice_bob_ethdos.pod as Box<dyn Any>)
            .downcast::<MainPod>()
            .unwrap();

        Ok(pod.verify()?)
    }

    #[test]
    fn test_main_mini_custom_1() -> frontend::Result<()> {
        let params = Params {
            max_input_signed_pods: 0,
            max_input_main_pods: 0,
            max_statements: 9,
            max_public_statements: 4,
            max_statement_args: 3,
            max_operation_args: 3,
            max_custom_predicate_arity: 3,
            max_custom_batch_size: 3,
            max_custom_predicate_wildcards: 4,
            max_custom_predicate_verifications: 2,
            ..Default::default()
        };
        println!("{:#?}", params);

        let mut cpb_builder = CustomPredicateBatchBuilder::new(params.clone(), "cpb".into());
        let stb0 = STB::new(NP::ValueOf)
            .arg(("id", key("score")))
            .arg(literal(42));
        let stb1 = STB::new(NP::Equal)
            .arg(("id", "secret_key"))
            .arg(("id", key("score")));
        let _ = cpb_builder.predicate_and(
            "pred_and",
            &["id"],
            &["secret_key"],
            &[stb0.clone(), stb1.clone()],
        )?;
        let _ = cpb_builder.predicate_or("pred_or", &["id"], &["secret_key"], &[stb0, stb1])?;
        let cpb = cpb_builder.finish();

        let cpb_and = CustomPredicateRef::new(cpb.clone(), 0);
        let _cpb_or = CustomPredicateRef::new(cpb.clone(), 1);

        let mut pod_builder = MainPodBuilder::new(&params);

        let st0 = pod_builder.priv_op(op!(new_entry, ("score", 42)))?;
        let st1 = pod_builder.priv_op(op!(new_entry, ("foo", 42)))?;
        let st2 = pod_builder.priv_op(op!(eq, st1.clone(), st0.clone()))?;

        let _st3 = pod_builder.priv_op(op!(custom, cpb_and.clone(), st0, st2))?;

        let mut prover = MockProver {};
        let pod = pod_builder.prove(&mut prover, &params)?;
        assert!(pod.pod.verify().is_ok());

        let mut prover = Prover {};
        let pod = pod_builder.prove(&mut prover, &params)?;
        crate::measure_gates_print!();

        let pod = (pod.pod as Box<dyn Any>).downcast::<MainPod>().unwrap();

        Ok(pod.verify()?)
    }
}
