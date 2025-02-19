use crate::middleware::{
    self, hash_str, AnchoredKey, Hash, MainPodInputs, NativeOperation, NativeStatement, NonePod,
    Params, Pod, PodId, PodProver, Statement, StatementArg, ToFields, KEY_TYPE, SELF,
};
use anyhow::{anyhow, Result};
use itertools::Itertools;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use std::any::Any;
use std::error::Error;
use std::fmt;

pub const VALUE_TYPE: &str = "MockMainPOD";

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn Pod>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum OperationArg {
    None,
    Index(usize),
}

impl OperationArg {
    fn is_none(&self) -> bool {
        matches!(self, OperationArg::None)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum OperationArgError {
    KeyNotFound,
    StatementNotFound,
}

impl std::fmt::Display for OperationArgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperationArgError::KeyNotFound => write!(f, "Key not found"),
            OperationArgError::StatementNotFound => write!(f, "Statement not found"),
        }
    }
}

impl std::error::Error for OperationArgError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Operation(pub NativeOperation, pub Vec<OperationArg>);

impl Operation {
    pub fn deref(&self, statements: &[Statement]) -> Result<crate::middleware::Operation> {
        let deref_args = self
            .1
            .iter()
            .flat_map(|arg| match arg {
                OperationArg::None => vec![],
                OperationArg::Index(i) => {
                    vec![statements[*i].clone().try_into()]
                }
            })
            .collect::<Result<Vec<crate::middleware::Statement>>>()?;
        middleware::Operation::op(self.0, &deref_args)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub NativeStatement, pub Vec<StatementArg>);

impl Statement {
    pub fn is_none(&self) -> bool {
        self.0 == NativeStatement::None
    }
}

impl ToFields for Statement {
    fn to_fields(self) -> (Vec<middleware::F>, usize) {
        let (native_statement_f, native_statement_f_len) = self.0.to_fields();
        let (vec_statementarg_f, vec_statementarg_f_len) = self
            .1
            .into_iter()
            .map(|statement_arg| statement_arg.to_fields())
            .fold((Vec::new(), 0), |mut acc, (f, l)| {
                acc.0.extend(f);
                acc.1 += l;
                acc
            });
        (
            [native_statement_f, vec_statementarg_f].concat(),
            native_statement_f_len + vec_statementarg_f_len,
        )
    }
}

impl TryInto<middleware::Statement> for Statement {
    type Error = anyhow::Error;
    fn try_into(self) -> Result<middleware::Statement> {
        type S = middleware::Statement;
        type NS = NativeStatement;
        type SA = StatementArg;
        let args = (
            self.1.get(0).cloned(),
            self.1.get(1).cloned(),
            self.1.get(2).cloned(),
        );
        Ok(match (self.0, args) {
            (NS::None, _) => S::None,
            (NS::ValueOf, (Some(SA::Key(ak)), Some(SA::Literal(v)), None)) => S::ValueOf(ak, v),
            (NS::Equal, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => S::Equal(ak1, ak2),
            (NS::NotEqual, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => S::NotEqual(ak1, ak2),
            (NS::Gt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => S::Gt(ak1, ak2),
            (NS::Lt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => S::Lt(ak1, ak2),
            (NS::Contains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => S::Contains(ak1, ak2),
            (NS::NotContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                S::NotContains(ak1, ak2)
            }
            (NS::SumOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                S::SumOf(ak1, ak2, ak3)
            }
            (NS::ProductOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                S::ProductOf(ak1, ak2, ak3)
            }
            (NS::MaxOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                S::MaxOf(ak1, ak2, ak3)
            }
            _ => Err(anyhow!("Malformed statement expression {}", self))?,
        })
    }
}

impl From<middleware::Statement> for Statement {
    fn from(s: middleware::Statement) -> Self {
        Statement(s.code(), s.args().into_iter().map(|arg| arg).collect())
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if !(!f.alternate() && arg.is_none()) {
                if i != 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}", arg)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if !(!f.alternate() && arg.is_none()) {
                if i != 0 {
                    write!(f, " ")?;
                }
                match arg {
                    OperationArg::None => write!(f, "none")?,
                    OperationArg::Index(i) => write!(f, "{:02}", i)?,
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct MockMainPod {
    params: Params,
    id: PodId,
    input_signed_pods: Vec<Box<dyn Pod>>,
    input_main_pods: Vec<Box<dyn Pod>>,
    // New statements introduced by this pod
    input_statements: Vec<Statement>,
    public_statements: Vec<Statement>,
    operations: Vec<Operation>,
    // All statements (inherited + new)
    statements: Vec<Statement>,
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
                && (i % self.params.max_public_statements == 0)
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
            fmt_statement_index(f, &st, op, i)?;
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
        write!(f, "\n")?;
    }
    Ok(())
}

fn fill_pad<T: Clone>(v: &mut Vec<T>, pad_value: T, len: usize) {
    if v.len() > len {
        panic!("length exceeded");
    }
    while v.len() < len {
        v.push(pad_value.clone());
    }
}

fn pad<T: Clone>(v: Vec<T>, pad_value: T, len: usize) -> Vec<T> {
    let v_len = v.len();
    [v, (v_len..len).map(|_| pad_value.clone()).collect()].concat()
}

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
    fn pad_statement(params: &Params, s: Statement) -> Statement {
        Statement(s.0, pad(s.1, StatementArg::None, params.max_statement_args))
    }
    fn pad_operation(params: &Params, op: Operation) -> Operation {
        Operation(
            op.0,
            pad(op.1, OperationArg::None, params.max_operation_args),
        )
    }

    fn layout_statements(params: &Params, inputs: &MainPodInputs) -> Vec<Statement> {
        let mut statements = Vec::new();

        // Input signed pods region
        let none_sig_pod: Box<dyn Pod> = Box::new(NonePod {});
        assert!(inputs.signed_pods.len() <= params.max_input_signed_pods);
        for i in 0..params.max_input_signed_pods {
            let pod = inputs
                .signed_pods
                .get(i)
                .map(|p| *p)
                .unwrap_or(&none_sig_pod);
            // TODO
            let sts = pod.pub_statements();
            assert!(sts.len() <= params.max_signed_pod_values);
            for j in 0..params.max_signed_pod_values {
                let mut st = sts.get(j).unwrap_or(&middleware::Statement::None).clone();
                statements.push(Self::pad_statement(params, st.into()));
            }
        }

        // Input main pods region
        let none_main_pod: Box<dyn Pod> = Box::new(NonePod {});
        assert!(inputs.main_pods.len() <= params.max_input_main_pods);
        for i in 0..params.max_input_main_pods {
            let pod = inputs
                .main_pods
                .get(i)
                .map(|p| *p)
                .unwrap_or(&none_main_pod);
            let sts = pod.pub_statements();
            assert!(sts.len() <= params.max_public_statements);
            for j in 0..params.max_public_statements {
                let mut st = sts.get(j).unwrap_or(&middleware::Statement::None).clone();
                statements.push(Self::pad_statement(params, st.into()));
            }
        }

        // Input statements
        assert!(inputs.statements.len() <= params.max_priv_statements());
        for i in 0..params.max_priv_statements() {
            let mut st = inputs
                .statements
                .get(i)
                .unwrap_or(&middleware::Statement::None)
                .clone();
            statements.push(Self::pad_statement(params, st.into()));
        }

        // Public statements
        assert!(inputs.public_statements.len() < params.max_public_statements);
        statements.push(Self::pad_statement(
            params,
            middleware::Statement::ValueOf(
                AnchoredKey(SELF, hash_str(KEY_TYPE)),
                middleware::Value(hash_str(VALUE_TYPE).0),
            )
            .into(),
        ));
        for i in 0..(params.max_public_statements - 1) {
            let st = inputs
                .public_statements
                .get(i)
                .unwrap_or(&middleware::Statement::None)
                .clone();
            statements.push(Self::pad_statement(params, st.into()));
        }

        statements
    }

    fn find_op_arg(statements: &[Statement], op_arg: &middleware::Statement) -> Result<OperationArg, OperationArgError> {
        statements
            .iter()
            .enumerate()
            .find_map(|(i, s)| (s == &op_arg.clone().into()))
            .map(OperationArg::Index)
                    .ok_or(OperationArgError::StatementNotFound)
    }

    fn process_private_statements_operations(
        params: &Params,
        statements: &[Statement],
        input_operations: &[middleware::Operation],
    ) -> Result<Vec<Operation>, OperationArgError> {
        let op_none = Self::operation_none(params);

        let mut operations = Vec::new();
        for i in 0..params.max_priv_statements() {
            let op = input_operations
                .get(i)
                .unwrap_or(&middleware::Operation::None)
                .clone();
            let mut mid_args = op.args();
            Self::pad_operation_args(params, &mut mid_args);
            let mut args = Vec::with_capacity(mid_args.len());
            for mid_arg in &mid_args {
                let op_arg = Self::find_op_arg(statements, mid_arg)?;
                args.push(op_arg)
            }
            operations.push(Operation(op.code(), args));
        }
        Ok(operations)
    }

    // NOTE: In this implementation public statements are always copies from previous statements,
    // so we fill in the operations accordingly.
    fn process_public_statements_operations(
        params: &Params,
        statements: &[Statement],
        mut operations: Vec<Operation>,
    ) -> Result<Vec<Operation>, OperationArgError> {
        let offset_public_statements = statements.len() - params.max_public_statements;
        operations.push(Operation(NativeOperation::NewEntry, vec![]));
        for i in 0..(params.max_public_statements - 1) {
            let st = &statements[offset_public_statements + i + 1];
            let mut op = if st.is_none() {
                Operation(NativeOperation::None, vec![])
            } else {
                let mid_arg = st.clone();
                Operation(
                    NativeOperation::CopyStatement,
                    // TODO
                    vec![Self::find_op_arg(statements, &mid_arg.try_into().unwrap())],
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
        let operations =
            Self::process_private_statements_operations(params, &statements, inputs.operations)?;
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
            .map(|s| Self::pad_statement(params, s.into()))
            .collect_vec();
        let public_statements =
            statements[statements.len() - params.max_public_statements..].to_vec();

        // get the id out of the public statements
        let id: PodId = PodId(hash_statements(&public_statements)?);

        Ok(Self {
            params: params.clone(),
            id,
            input_signed_pods,
            input_main_pods,
            input_statements,
            public_statements,
            statements,
            operations,
        })
    }

    fn statement_none(params: &Params) -> Statement {
        let mut args = Vec::with_capacity(params.max_statement_args);
        Self::pad_statement_args(&params, &mut args);
        Statement(NativeStatement::None, args)
    }

    fn operation_none(params: &Params) -> Operation {
        Self::pad_operation(params, Operation(NativeOperation::None, vec![]))
    }

    fn pad_statement_args(params: &Params, args: &mut Vec<StatementArg>) {
        fill_pad(args, StatementArg::None, params.max_statement_args)
    }

    fn pad_operation_args(params: &Params, args: &mut Vec<middleware::Statement>) {
        fill_pad(args, middleware::Statement::None, params.max_operation_args)
    }
}

pub fn hash_statements(statements: &[Statement]) -> Result<middleware::Hash> {
    let field_elems = statements
        .into_iter()
        .flat_map(|statement| statement.clone().to_fields().0)
        .collect::<Vec<_>>();
    Ok(Hash(PoseidonHash::hash_no_pad(&field_elems).elements))
}

impl Pod for MockMainPod {
    fn verify(&self) -> bool {
        let input_statement_offset = self.offset_input_statements();
        // get the input_statements from the self.statements
        let input_statements = &self.statements[input_statement_offset..];
        // get the id out of the public statements, and ensure it is equal to self.id
        let ids_match = self.id == PodId(hash_statements(&self.public_statements).unwrap());
        // find a ValueOf statement from the public statements with key=KEY_TYPE and check that the
        // value is PodType::MockMainPod
        let has_type_statement = self
            .public_statements
            .iter()
            .find(|s| {
                s.0 == NativeStatement::ValueOf
                    && s.1.len() > 0
                    && if let StatementArg::Key(AnchoredKey(pod_id, key_hash)) = s.1[0] {
                        pod_id == SELF && key_hash == hash_str(KEY_TYPE)
                    } else {
                        false
                    }
            })
            .is_some();
        // check that all `input_statements` of type `ValueOf` with origin=SELF have unique keys
        // (no duplicates)
        // TODO: Instead of doing this, do a uniqueness check when verifying the output of a
        // `NewValue` operation.
        let value_ofs_unique = {
            let key_id_pairs = input_statements
                .into_iter()
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
                .filter(|(i, s)| s.0 == NativeStatement::ValueOf)
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
        // verify that all `input_statements` are correctly generated
        // by `self.operations` (where each operation can only access previous statements)
        let statement_check = input_statements
            .iter()
            .enumerate()
            .map(|(i, s)| {
                self.operations[i]
                    .deref(&self.statements[..input_statement_offset + i])
                    .unwrap()
                    .check(&s.clone().try_into().unwrap())
            })
            .collect::<Result<Vec<_>>>()
            .unwrap();
        ids_match && has_type_statement && value_ofs_unique & statement_check.into_iter().all(|b| b)
    }
    fn id(&self) -> PodId {
        self.id
    }
    fn pub_statements(&self) -> Vec<middleware::Statement> {
        // return the public statements, where when origin=SELF is replaced by origin=self.id()
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
                            _ => sa.clone(),
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
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::mock_signed::MockSigner;
    use crate::examples::{great_boy_pod_full_flow, tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_sign_pod_builders};
    use crate::middleware;

    #[test]
    fn test_mock_main_zu_kyc() {
        let params = middleware::Params::default();

        let (gov_id_builder, pay_stub_builder) = zu_kyc_sign_pod_builders(&params);
        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id_pod = gov_id_builder.sign(&mut signer).unwrap();
        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub_pod = pay_stub_builder.sign(&mut signer).unwrap();
        let kyc_builder = zu_kyc_pod_builder(&params, &gov_id_pod, &pay_stub_pod);

        let mut prover = MockProver {};
        let kyc_pod = kyc_builder.prove(&mut prover).unwrap();
        let pod = kyc_pod.pod.into_any().downcast::<MockMainPod>().unwrap();

        println!("{:#}", pod);

        assert_eq!(pod.verify(), true); // TODO
                                        // println!("id: {}", pod.id());
                                        // println!("pub_statements: {:?}", pod.pub_statements());
    }

    #[test]
    fn test_mock_main_great_boy() {
        let great_boy_builder = great_boy_pod_full_flow();

        let mut prover = MockProver {};
        let great_boy_pod = great_boy_builder.prove(&mut prover).unwrap();
        let pod = great_boy_pod
            .pod
            .into_any()
            .downcast::<MockMainPod>()
            .unwrap();

        println!("{}", pod);

        assert_eq!(pod.verify(), true);
    }

    #[test]
    fn test_mock_main_tickets() {
        let tickets_builder = tickets_pod_full_flow();
        let mut prover = MockProver {};
        let proof_pod = tickets_builder.prove(&mut prover).unwrap();
        let pod = proof_pod.pod.into_any().downcast::<MockMainPod>().unwrap();

        println!("{}", pod);
        assert_eq!(pod.verify(), true); 
    }
}
