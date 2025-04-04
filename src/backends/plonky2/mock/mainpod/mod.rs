use anyhow::{anyhow, Result};
use base64::prelude::*;
use itertools::Itertools;
use log::error;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fmt;

use crate::{
    backends::plonky2::primitives::merkletree::MerkleProof,
    middleware::{
        self, hash_str, AnchoredKey, Hash, MainPodInputs, NativeOperation, NativePredicate,
        NonePod, OperationType, Params, Pod, PodId, PodProver, PodType, Predicate, StatementArg,
        ToFields, KEY_TYPE, SELF,
    },
};

mod operation;
mod statement;
pub use operation::*;
pub use statement::*;

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MockMainPod {
    params: Params,
    id: PodId,
    //   input_signed_pods: Vec<Box<dyn Pod>>,
    //   input_main_pods: Vec<Box<dyn Pod>>,
    // New statements introduced by this pod
    //   input_statements: Vec<Statement>,
    public_statements: Vec<Statement>,
    operations: Vec<Operation>,
    // All statements (inherited + new)
    statements: Vec<Statement>,
    // All Merkle proofs
    // TODO: Use a backend-specific representation
    merkle_proofs: Vec<MerkleProof>,
}

impl fmt::Display for MockMainPod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "MockMainPod ({}):", self.id)?;
        // TODO print input signed pods id and type
        // TODO print input main pods id and type
        let offset_input_main_pods = self.offset_input_main_pods();
        let offset_input_statements = self.offset_input_statements();
        let offset_public_statements = self.offset_public_statements();
        for (i, st) in self.statements.iter().enumerate() {
            if (i < self.offset_input_main_pods()) && (i % self.params.max_signed_pod_values == 0) {
                writeln!(
                    f,
                    "  from input SignedPod {}:",
                    i / self.params.max_signed_pod_values
                )?;
            }
            if (i >= offset_input_main_pods)
                && (i < offset_input_statements)
                && ((i - offset_input_main_pods) % self.params.max_public_statements == 0)
            {
                writeln!(
                    f,
                    "  from input MainPod {}:",
                    (i - offset_input_main_pods) / self.params.max_signed_pod_values
                )?;
            }
            if i == offset_input_statements {
                writeln!(f, "  private statements:")?;
            }
            if i == offset_public_statements {
                writeln!(f, "  public statements:")?;
            }

            let op = (i >= offset_input_statements)
                .then(|| &self.operations[i - offset_input_statements]);
            fmt_statement_index(f, st, op, i)?;
        }
        Ok(())
    }
}

fn fmt_statement_index(
    f: &mut fmt::Formatter,
    st: &Statement,
    op: Option<&Operation>,
    index: usize,
) -> fmt::Result {
    if !(!f.alternate() && st.is_none()) {
        write!(f, "    {:03}. ", index)?;
        if f.alternate() {
            write!(f, "{:#}", &st)?;
        } else {
            write!(f, "{}", &st)?;
        }
        if let Some(op) = op {
            write!(f, " <- ")?;
            if f.alternate() {
                write!(f, "{:#}", op)?;
            } else {
                write!(f, "{}", op)?;
            }
        }
        writeln!(f)?;
    }
    Ok(())
}

pub fn fill_pad<T: Clone>(v: &mut Vec<T>, pad_value: T, len: usize) {
    if v.len() > len {
        panic!("length exceeded");
    }
    while v.len() < len {
        v.push(pad_value.clone());
    }
}

/// Inputs are sorted as:
/// - SignedPods
/// - MainPods
/// - private Statements
/// - public Statements
impl MockMainPod {
    fn offset_input_signed_pods(&self) -> usize {
        0
    }
    fn offset_input_main_pods(&self) -> usize {
        self.params.max_input_signed_pods * self.params.max_signed_pod_values
    }
    fn offset_input_statements(&self) -> usize {
        self.offset_input_main_pods()
            + self.params.max_input_main_pods * self.params.max_public_statements
    }
    fn offset_public_statements(&self) -> usize {
        self.offset_input_statements() + self.params.max_priv_statements()
    }
    fn pad_statement(params: &Params, s: &mut Statement) {
        fill_pad(&mut s.1, StatementArg::None, params.max_statement_args)
    }
    fn pad_operation(params: &Params, op: &mut Operation) {
        fill_pad(&mut op.1, OperationArg::None, params.max_operation_args)
    }

    /// Returns the statements from the given MainPodInputs, padding to the
    /// respective max lengths defined at the given Params.
    pub(crate) fn layout_statements(params: &Params, inputs: &MainPodInputs) -> Vec<Statement> {
        let mut statements = Vec::new();

        // Input signed pods region
        let none_sig_pod: Box<dyn Pod> = Box::new(NonePod {});
        assert!(inputs.signed_pods.len() <= params.max_input_signed_pods);
        for i in 0..params.max_input_signed_pods {
            let pod = inputs.signed_pods.get(i).copied().unwrap_or(&none_sig_pod);
            let sts = pod.pub_statements();
            assert!(sts.len() <= params.max_signed_pod_values);
            for j in 0..params.max_signed_pod_values {
                let mut st = sts
                    .get(j)
                    .unwrap_or(&middleware::Statement::None)
                    .clone()
                    .into();
                Self::pad_statement(params, &mut st);
                statements.push(st);
            }
        }

        // Input main pods region
        let none_main_pod: Box<dyn Pod> = Box::new(NonePod {});
        assert!(inputs.main_pods.len() <= params.max_input_main_pods);
        for i in 0..params.max_input_main_pods {
            let pod = inputs.main_pods.get(i).copied().unwrap_or(&none_main_pod);
            let sts = pod.pub_statements();
            assert!(sts.len() <= params.max_public_statements);
            for j in 0..params.max_public_statements {
                let mut st = sts
                    .get(j)
                    .unwrap_or(&middleware::Statement::None)
                    .clone()
                    .into();
                Self::pad_statement(params, &mut st);
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
            Self::pad_statement(params, &mut st);
            statements.push(st);
        }

        // Public statements
        assert!(inputs.public_statements.len() < params.max_public_statements);
        let mut type_st = middleware::Statement::ValueOf(
            AnchoredKey(SELF, hash_str(KEY_TYPE)),
            middleware::Value::from(PodType::MockMain),
        )
        .into();
        Self::pad_statement(params, &mut type_st);
        statements.push(type_st);

        for i in 0..(params.max_public_statements - 1) {
            let mut st = inputs
                .public_statements
                .get(i)
                .unwrap_or(&middleware::Statement::None)
                .clone()
                .into();
            Self::pad_statement(params, &mut st);
            statements.push(st);
        }

        statements
    }

    fn find_op_arg(
        statements: &[Statement],
        op_arg: &middleware::Statement,
    ) -> Result<OperationArg> {
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

    fn find_op_aux(
        merkle_proofs: &[MerkleProof],
        op_aux: &middleware::OperationAux,
    ) -> Result<OperationAux> {
        match op_aux {
            middleware::OperationAux::None => Ok(OperationAux::None),
            middleware::OperationAux::MerkleProof(pf_arg) => merkle_proofs
                .iter()
                .enumerate()
                .find_map(|(i, pf)| (pf == pf_arg).then_some(i))
                .map(OperationAux::MerkleProofIndex)
                .ok_or(anyhow!(
                    "Merkle proof corresponding to op arg {} not found",
                    op_aux
                )),
        }
    }

    pub(crate) fn process_private_statements_operations(
        params: &Params,
        statements: &[Statement],
        merkle_proofs: &[MerkleProof],
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
                .map(|mid_arg| Self::find_op_arg(statements, mid_arg))
                .collect::<Result<Vec<_>>>()?;

            let mid_aux = op.aux();
            let aux = Self::find_op_aux(merkle_proofs, &mid_aux)?;

            Self::pad_operation_args(params, &mut args);
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
                    vec![Self::find_op_arg(statements, &mid_arg.try_into()?)?],
                    OperationAux::None,
                )
            };
            fill_pad(&mut op.1, OperationArg::None, params.max_operation_args);
            operations.push(op);
        }
        Ok(operations)
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        // TODO: Figure out a way to handle public statements.  For example, in the public slots
        // use copy operations taking the private statements that need to be public.  We may change
        // the MainPodInputs type to accommodate for that.
        // TODO: Insert a new public statement of ValueOf with `key=KEY_TYPE,
        // value=PodType::MockMainPod`
        let statements = Self::layout_statements(params, &inputs);
        let merkle_proofs = inputs
            .operations
            .iter()
            .flat_map(|op| match op {
                middleware::Operation::ContainsFromEntries(_, _, _, pf) => Some(pf.clone()),
                middleware::Operation::NotContainsFromEntries(_, _, pf) => Some(pf.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let operations = Self::process_private_statements_operations(
            params,
            &statements,
            &merkle_proofs,
            inputs.operations,
        )?;
        let operations =
            Self::process_public_statements_operations(params, &statements, operations)?;

        let input_signed_pods = inputs
            .signed_pods
            .iter()
            .map(|p| (*p).clone())
            .collect_vec();
        let input_main_pods = inputs.main_pods.iter().map(|p| (*p).clone()).collect_vec();
        let input_statements = inputs
            .statements
            .iter()
            .cloned()
            .map(|s| {
                let mut s = s.into();
                Self::pad_statement(params, &mut s);
                s
            })
            .collect_vec();
        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();

        // get the id out of the public statements
        let id: PodId = PodId(hash_statements(&public_statements, params));

        Ok(Self {
            params: params.clone(),
            id,
            //  input_signed_pods,
            //  input_main_pods,
            //  input_statements,
            public_statements,
            statements,
            operations,
            merkle_proofs,
        })
    }

    fn statement_none(params: &Params) -> Statement {
        let mut args = Vec::with_capacity(params.max_statement_args);
        Self::pad_statement_args(params, &mut args);
        Statement(Predicate::Native(NativePredicate::None), args)
    }

    fn operation_none(params: &Params) -> Operation {
        let mut op = Operation(
            OperationType::Native(NativeOperation::None),
            vec![],
            OperationAux::None,
        );
        fill_pad(&mut op.1, OperationArg::None, params.max_operation_args);
        op
    }

    fn pad_statement_args(params: &Params, args: &mut Vec<StatementArg>) {
        fill_pad(args, StatementArg::None, params.max_statement_args)
    }

    fn pad_operation_args(params: &Params, args: &mut Vec<OperationArg>) {
        fill_pad(args, OperationArg::None, params.max_operation_args)
    }

    pub fn deserialize(serialized: String) -> Result<Self> {
        let proof = String::from_utf8(BASE64_STANDARD.decode(&serialized)?)
            .map_err(|e| anyhow::anyhow!("Invalid base64 encoding: {}", e))?;
        let pod: MockMainPod = serde_json::from_str(&proof)
            .map_err(|e| anyhow::anyhow!("Failed to parse proof: {}", e))?;

        Ok(pod)
    }
}

pub fn hash_statements(statements: &[Statement], _params: &Params) -> middleware::Hash {
    let field_elems = statements
        .iter()
        .flat_map(|statement| statement.clone().to_fields(_params))
        .collect::<Vec<_>>();
    Hash(PoseidonHash::hash_no_pad(&field_elems).elements)
}

impl Pod for MockMainPod {
    fn verify(&self) -> Result<()> {
        // 1. TODO: Verify input pods

        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];
        // 2. get the id out of the public statements, and ensure it is equal to self.id
        let ids_match = self.id == PodId(hash_statements(&self.public_statements, &self.params));
        // find a ValueOf statement from the public statements with key=KEY_TYPE and check that the
        // value is PodType::MockMainPod
        let has_type_statement = self
            .public_statements
            .iter()
            .find(|s| {
                s.0 == Predicate::Native(NativePredicate::ValueOf)
                    && !s.1.is_empty()
                    && if let StatementArg::Key(AnchoredKey(pod_id, key_hash)) = s.1[0] {
                        pod_id == SELF && key_hash == hash_str(KEY_TYPE)
                    } else {
                        false
                    }
            })
            .is_some();
        // 3. check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys
        // (no duplicates)
        // TODO: Instead of doing this, do a uniqueness check when verifying the output of a
        // `NewValue` operation.
        let value_ofs_unique = {
            let key_id_pairs = input_statements
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    (
                        // Separate private from public statements.
                        if i < self.params.max_priv_statements() {
                            0
                        } else {
                            1
                        },
                        s,
                    )
                })
                .filter(|(_, s)| s.0 == Predicate::Native(NativePredicate::ValueOf))
                .flat_map(|(i, s)| {
                    if let StatementArg::Key(ak) = &s.1[0] {
                        vec![(i, ak.1, ak.0)]
                    } else {
                        vec![]
                    }
                })
                .collect::<Vec<_>>();
            !(0..key_id_pairs.len() - 1).any(|i| key_id_pairs[i + 1..].contains(&key_id_pairs[i]))
        };
        // 4. TODO: Verify type

        // 5. verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = input_statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                self.operations[i]
                    .deref(
                        &self.statements[..input_statement_offset + i],
                        &self.merkle_proofs,
                    )
                    .unwrap()
                    .check_and_log(&self.params, &s.clone().try_into().unwrap())
            })
            .collect::<Result<Vec<_>>>()
            .unwrap();
        if !ids_match {
            return Err(anyhow!("Verification failed: POD ID is incorrect."));
        }
        if !has_type_statement {
            return Err(anyhow!(
                "Verification failed: POD does not have type statement."
            ));
        }
        if !value_ofs_unique {
            return Err(anyhow!("Verification failed: Repeated ValueOf"));
        }
        if !statement_check.iter().all(|b| *b) {
            return Err(anyhow!("Verification failed: Statement did not check."));
        }
        Ok(())
    }
    fn id(&self) -> PodId {
        self.id
    }
    fn pub_statements(&self) -> Vec<middleware::Statement> {
        // return the public statements, where when origin=SELF is replaced by origin=self.id()
        // By convention we expect the KEY_TYPE to be the first statement
        self.statements
            .iter()
            .skip(self.offset_public_statements())
            .cloned()
            .map(|statement| {
                Statement(
                    statement.0.clone(),
                    statement
                        .1
                        .iter()
                        .map(|sa| match &sa {
                            StatementArg::Key(AnchoredKey(pod_id, h)) if *pod_id == SELF => {
                                StatementArg::Key(AnchoredKey(self.id(), *h))
                            }
                            _ => *sa,
                        })
                        .collect(),
                )
                .try_into()
                .unwrap()
            })
            .collect()
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }

    fn serialized_proof(&self) -> String {
        BASE64_STANDARD.encode(serde_json::to_string(self).unwrap())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::plonky2::mock::signedpod::MockSigner;
    use crate::examples::{
        great_boy_pod_full_flow, tickets_pod_full_flow, zu_kyc_pod_builder,
        zu_kyc_sign_pod_builders,
    };
    use crate::middleware;
    use crate::middleware::containers::Set;

    #[test]
    fn test_mock_main_zu_kyc() -> Result<()> {
        let params = middleware::Params::default();
        let sanctions_values = ["A343434340"].map(|s| crate::frontend::Value::from(s));
        let sanction_set = crate::frontend::Value::Set(crate::frontend::containers::Set::new(
            sanctions_values.to_vec(),
        )?);

        let (gov_id_builder, pay_stub_builder, sanction_list_builder) =
            zu_kyc_sign_pod_builders(&params, &sanction_set);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id_pod = gov_id_builder.sign(&mut signer)?;
        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub_pod = pay_stub_builder.sign(&mut signer)?;
        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list_pod = sanction_list_builder.sign(&mut signer)?;
        let kyc_builder =
            zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod, &sanction_list_pod)?;

        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover, &params)?;
        let pod = kyc_pod.pod.into_any().downcast::<MockMainPod>().unwrap();

        println!("{:#}", pod);

        pod.verify()?; // TODO
                       // println!("id: {}", pod.id());
                       // println!("pub_statements: {:?}", pod.pub_statements());
        Ok(())
    }

    #[test]
    fn test_mock_main_great_boy() -> Result<()> {
        let params = middleware::Params::default();
        let great_boy_builder = great_boy_pod_full_flow()?;

        let mut prover = MockProver {};
        let great_boy_pod = great_boy_builder.prove(&mut prover, &params)?;
        let pod = great_boy_pod
            .pod
            .into_any()
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{}", pod);

        pod.verify()?;

        Ok(())
    }

    #[test]
    fn test_mock_main_tickets() -> Result<()> {
        let params = middleware::Params::default();
        let tickets_builder = tickets_pod_full_flow()?;
        let mut prover = MockProver {};
        let proof_pod = tickets_builder.prove(&mut prover, &params)?;
        let pod = proof_pod.pod.into_any().downcast::<MockMainPod>().unwrap();

        println!("{}", pod);
        pod.verify()?;

        Ok(())
    }
}
