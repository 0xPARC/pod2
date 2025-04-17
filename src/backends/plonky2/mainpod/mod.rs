pub mod operation;
pub mod statement;
use std::any::Any;

use anyhow::{anyhow, Result};
use itertools::Itertools;
pub use operation::*;
use plonky2::{
    hash::poseidon::PoseidonHash,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, config::Hasher,
        proof::ProofWithPublicInputs,
    },
};
pub use statement::*;

use crate::{
    backends::plonky2::{
        basetypes::{C, D},
        circuits::mainpod::{MainPodVerifyCircuit, MainPodVerifyInput},
        primitives::{merkletree, merkletree::MerkleClaimAndProof},
        signedpod::SignedPod,
    },
    middleware::{
        self, AnchoredKey, Hash, MainPodInputs, NativeOperation, NonePod, OperationType, Params,
        Pod, PodId, PodProver, PodType, StatementArg, ToFields, F, KEY_TYPE, SELF,
    },
};

/// Hash a list of public statements to derive the PodId
pub(crate) fn hash_statements(statements: &[Statement], _params: &Params) -> middleware::Hash {
    let field_elems = statements
        .iter()
        .flat_map(|statement| statement.clone().to_fields(_params))
        .collect::<Vec<_>>();
    Hash(PoseidonHash::hash_no_pad(&field_elems).elements)
}

/// Extracts and pads Merkle proofs from Contains/NotContains ops.
pub(crate) fn extract_merkle_proofs(
    params: &Params,
    operations: &[middleware::Operation],
) -> Result<Vec<MerkleClaimAndProof>> {
    let mut merkle_proofs = operations
        .iter()
        .flat_map(|op| match op {
            middleware::Operation::ContainsFromEntries(
                middleware::Statement::ValueOf(_, root),
                middleware::Statement::ValueOf(_, key),
                middleware::Statement::ValueOf(_, value),
                pf,
            ) => Some(MerkleClaimAndProof::new(
                params.max_depth_mt_gadget,
                Hash::from(root.raw()),
                key.raw(),
                Some(value.raw()),
                pf,
            )),
            middleware::Operation::NotContainsFromEntries(
                middleware::Statement::ValueOf(_, root),
                middleware::Statement::ValueOf(_, key),
                pf,
            ) => Some(MerkleClaimAndProof::new(
                params.max_depth_mt_gadget,
                Hash::from(root.raw()),
                key.raw(),
                None,
                pf,
            )),
            _ => None,
        })
        .collect::<Result<Vec<_>>>()?;
    if merkle_proofs.len() > params.max_merkle_proofs {
        Err(anyhow!(
            "The number of required Merkle proofs ({}) exceeds the maximum number ({}).",
            merkle_proofs.len(),
            params.max_merkle_proofs
        ))
    } else {
        fill_pad(
            &mut merkle_proofs,
            MerkleClaimAndProof::empty(params.max_depth_mt_gadget),
            params.max_merkle_proofs,
        );
        Ok(merkle_proofs)
    }
}

/// Find the operation argument statement in the list of previous statements and return the index.
fn find_op_arg(statements: &[Statement], op_arg: &middleware::Statement) -> Result<OperationArg> {
    match op_arg {
        middleware::Statement::None => Ok(OperationArg::None),
        _ => statements
            .iter()
            .enumerate()
            .find_map(|(i, s)| {
                (&middleware::Statement::try_from(s.clone()).ok()? == op_arg).then_some(i)
            })
            .map(OperationArg::Index)
            .ok_or(anyhow!(
                "Statement corresponding to op arg {} not found",
                op_arg
            )),
    }
}

/// Find the operation auxiliary data in the list of auxiliary data and return the index.
fn find_op_aux(
    merkle_proofs: &[MerkleClaimAndProof],
    op_aux: &middleware::OperationAux,
) -> Result<OperationAux> {
    match op_aux {
        middleware::OperationAux::None => Ok(OperationAux::None),
        middleware::OperationAux::MerkleProof(pf_arg) => merkle_proofs
            .iter()
            .enumerate()
            .find_map(|(i, pf)| {
                pf.clone()
                    .try_into()
                    .ok()
                    .and_then(|mid_pf: merkletree::MerkleProof| (&mid_pf == pf_arg).then_some(i))
            })
            .map(OperationAux::MerkleProofIndex)
            .ok_or(anyhow!(
                "Merkle proof corresponding to op arg {} not found",
                op_aux
            )),
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

fn pad_statement(params: &Params, s: &mut Statement) {
    fill_pad(&mut s.1, StatementArg::None, params.max_statement_args)
}

fn pad_operation_args(params: &Params, args: &mut Vec<OperationArg>) {
    fill_pad(args, OperationArg::None, params.max_operation_args)
}

/// Returns the statements from the given MainPodInputs, padding to the
/// respective max lengths defined at the given Params.
pub(crate) fn layout_statements(params: &Params, inputs: &MainPodInputs) -> Vec<Statement> {
    let mut statements = Vec::new();

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

        let mid_aux = op.aux();
        let aux = find_op_aux(merkle_proofs, &mid_aux)?;

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

impl PodProver for Prover {
    // TODO: Be consistent on where we apply the padding, here, or in the set_targets?
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let main_pod = MainPodVerifyCircuit {
            params: params.clone(),
        }
        .eval(&mut builder)?;

        let mut pw = PartialWitness::<F>::new();
        let signed_pods_input: Vec<SignedPod> = inputs
            .signed_pods
            .iter()
            .map(|p| {
                let p = p
                    .as_any()
                    .downcast_ref::<SignedPod>()
                    .expect("type SignedPod");
                p.clone()
            })
            .collect_vec();

        let merkle_proofs = extract_merkle_proofs(params, inputs.operations)?;

        let statements = layout_statements(params, &inputs);
        let operations = process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            inputs.operations,
        )?;
        let operations = process_public_statements_operations(params, &statements, operations)?;

        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();
        // get the id out of the public statements
        let id: PodId = PodId(hash_statements(&public_statements, params));

        let input = MainPodVerifyInput {
            signed_pods: signed_pods_input,
            statements: statements[statements.len() - params.max_statements..].to_vec(),
            operations,
            merkle_proofs,
        };
        main_pod.set_targets(&mut pw, &input)?;

        // generate & verify proof
        let data = builder.build::<C>();
        let proof = data.prove(pw)?;

        Ok(Box::new(MainPod {
            params: params.clone(),
            id,
            public_statements,
            proof,
        }))
    }
}

#[derive(Clone, Debug)]
pub struct MainPod {
    params: Params,
    id: PodId,
    public_statements: Vec<Statement>,
    proof: ProofWithPublicInputs<F, C, 2>,
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

impl Pod for MainPod {
    fn verify(&self) -> Result<()> {
        // 2. get the id out of the public statements
        let id: PodId = PodId(hash_statements(&self.public_statements, &self.params));
        if id != self.id {
            return Err(anyhow!(
                "id does not match, expected {}, computed {}",
                self.id,
                id
            ));
        }

        // 1, 3, 4, 5 verification via the zkSNARK proof
        // TODO: cache these artefacts
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let _main_pod = MainPodVerifyCircuit {
            params: self.params.clone(),
        }
        .eval(&mut builder)?;

        let data = builder.build::<C>();
        data.verify(self.proof.clone())
            .map_err(|e| anyhow!("MainPod proof verification failure: {:?}", e))
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

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn serialized_proof(&self) -> String {
        todo!()
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
        examples::{zu_kyc_pod_builder, zu_kyc_sign_pod_builders},
        frontend, middleware,
        middleware::RawValue,
        op,
    };

    #[test]
    fn test_main_zu_kyc() -> Result<()> {
        let params = middleware::Params {
            // Currently the circuit uses random access that only supports vectors of length 64.
            // With max_input_main_pods=3 we need random access to a vector of length 73.
            max_input_main_pods: 1,
            ..Default::default()
        };

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
        let pod = kyc_pod.pod.into_any().downcast::<MainPod>().unwrap();

        pod.verify()
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
        let pod = kyc_pod.pod.into_any().downcast::<MockMainPod>().unwrap();
        pod.verify().unwrap();
        println!("{:#}", pod);

        // Real
        let mut prover = Prover {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params).unwrap();
        let pod = kyc_pod.pod.into_any().downcast::<MainPod>().unwrap();
        pod.verify().unwrap()
    }
}
