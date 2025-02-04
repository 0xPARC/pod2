use crate::merkletree::MerkleTree;
use crate::middleware::{
    self, hash_str, Hash, MainPod, MainPodInputs, NativeOperation, NativeStatement, NoneMainPod,
    NoneSignedPod, Params, PodId, PodProver, PodType, SignedPod, Statement, StatementArg, Value,
    KEY_SIGNER, KEY_TYPE,
};
use anyhow::Result;
use itertools::Itertools;
use std::any::Any;
use std::collections::HashMap;

pub struct MockProver {}

impl PodProver for MockProver {
    fn prove(&mut self, params: &Params, inputs: MainPodInputs) -> Result<Box<dyn MainPod>> {
        Ok(Box::new(MockMainPod::new(params, inputs)?))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum OperationArg {
    None,
    Index(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Operation(pub NativeOperation, pub Vec<OperationArg>);

#[derive(Clone, Debug)]
pub struct MockMainPod {
    id: PodId,
    input_signed_pods: Vec<Box<dyn SignedPod>>,
    input_main_pods: Vec<Box<dyn MainPod>>,
    // New statements introduced by this pod
    input_statements: Vec<(bool, Statement)>,
    operations: Vec<Operation>,
    // All statements (inherited + new)
    statements: Vec<Statement>,
}

fn fill_pad<T: Clone>(v: &mut Vec<T>, pad_value: T, len: usize) {
    if v.len() > len {
        panic!("length exceeded");
    }
    while v.len() < len {
        v.push(pad_value.clone());
    }
}

impl MockMainPod {
    fn layout_statements(params: &Params, inputs: &MainPodInputs) -> Vec<Statement> {
        let mut statements = Vec::new();

        let st_none = Self::statement_none(params);

        // Input signed pods region
        let none_sig_pod: Box<dyn SignedPod> = Box::new(NoneSignedPod {});
        for i in 0..params.max_input_signed_pods {
            let pod = inputs
                .signed_pods
                .get(i)
                .map(|p| *p)
                .unwrap_or(&none_sig_pod);
            for j in 0..params.max_signed_pod_values {
                let sts = pod.pub_statements();
                let mut st = sts.get(j).unwrap_or(&st_none).clone();
                Self::pad_statement_args(params, &mut st.1);
                statements.push(st);
            }
        }

        // Input main pods region
        let none_main_pod: Box<dyn MainPod> = Box::new(NoneMainPod {});
        for i in 0..params.max_input_main_pods {
            let pod = inputs
                .main_pods
                .get(i)
                .map(|p| *p)
                .unwrap_or(&none_main_pod);
            for j in 0..params.max_public_statements {
                let sts = pod.pub_statements();
                let mut st = sts.get(j).unwrap_or(&st_none).clone();
                Self::pad_statement_args(params, &mut st.1);
                statements.push(st);
            }
        }

        // Input statements
        for i in 0..params.max_statements {
            let mut st = inputs
                .statements
                .get(i)
                .map(|s| &s.1)
                .unwrap_or(&st_none)
                .clone();
            Self::pad_statement_args(params, &mut st.1);
            statements.push(st);
        }

        statements
    }

    fn find_op_arg(statements: &[Statement], op_arg: &middleware::OperationArg) -> OperationArg {
        match op_arg {
            middleware::OperationArg::None => OperationArg::None,
            middleware::OperationArg::Key(k) => OperationArg::Index(
                statements
                    .iter()
                    .enumerate()
                    .find_map(|(i, s)| match s.0 {
                        NativeStatement::ValueOf => match &s.1[0] {
                            StatementArg::Key(sk) => (sk == k).then_some(i),
                            _ => None,
                        },
                        _ => None,
                    })
                    .unwrap(),
            ),
            middleware::OperationArg::Statement(st) => OperationArg::Index(
                statements
                    .iter()
                    .enumerate()
                    .find_map(|(i, s)| (s == st).then_some(i))
                    .unwrap(),
            ),
        }
    }

    fn process_operations(
        params: &Params,
        statements: &[Statement],
        input_operations: &[middleware::Operation],
    ) -> Vec<Operation> {
        let op_none = Self::operation_none(params);

        let mut operations = Vec::new();
        for i in 0..params.max_statements {
            let op = input_operations.get(i).unwrap_or(&op_none).clone();
            let mut mid_args = op.1;
            Self::pad_operation_args(params, &mut mid_args);
            let mut args = Vec::with_capacity(mid_args.len());
            for mid_arg in &mid_args {
                args.push(Self::find_op_arg(statements, mid_arg));
            }
            operations.push(Operation(op.0, args));
        }
        operations
    }

    pub fn new(params: &Params, inputs: MainPodInputs) -> Result<Self> {
        let statements = Self::layout_statements(params, &inputs);
        let operations = Self::process_operations(params, &statements, inputs.operations);

        let input_signed_pods = inputs
            .signed_pods
            .iter()
            .map(|p| (*p).clone())
            .collect_vec();
        let input_main_pods = inputs.main_pods.iter().map(|p| (*p).clone()).collect_vec();
        let input_statements = inputs.statements.iter().cloned().collect_vec();
        Ok(Self {
            id: PodId::default(), // TODO
            input_signed_pods,
            input_main_pods,
            input_statements,
            statements,
            operations,
        })
    }

    fn statement_none(params: &Params) -> Statement {
        let mut args = Vec::with_capacity(params.max_statement_args);
        Self::pad_statement_args(&params, &mut args);
        Statement(NativeStatement::None, args)
    }

    fn operation_none(params: &Params) -> middleware::Operation {
        let mut args = Vec::with_capacity(params.max_operation_args);
        Self::pad_operation_args(&params, &mut args);
        middleware::Operation(NativeOperation::None, args)
    }

    fn pad_statement_args(params: &Params, args: &mut Vec<StatementArg>) {
        fill_pad(args, StatementArg::None, params.max_statement_args)
    }

    fn pad_operation_args(params: &Params, args: &mut Vec<middleware::OperationArg>) {
        fill_pad(
            args,
            middleware::OperationArg::None,
            params.max_operation_args,
        )
    }
}

impl MainPod for MockMainPod {
    fn verify(&self) -> bool {
        todo!()
    }
    fn id(&self) -> PodId {
        self.id
    }
    fn pub_statements(&self) -> Vec<Statement> {
        self.input_statements
            .iter()
            .filter_map(|(is_public, s)| is_public.then(|| s))
            .cloned()
            .collect()
    }

    fn into_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}
