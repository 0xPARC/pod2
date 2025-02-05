//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use anyhow::Result;
use itertools::Itertools;
use plonky2::field::types::Field;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;
use std::io::{self, Write};

use crate::middleware::{
    self, hash_str, Hash, MainPodInputs, NativeOperation, NativeStatement, Params, PodId,
    PodProver, PodSigner, F, SELF,
};

/// This type is just for presentation purposes.
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub enum PodClass {
    #[default]
    Signed,
    Main,
}

// An Origin, which represents a reference to an ancestor POD.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Origin(pub PodClass, pub PodId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleTree {
    pub root: u8, // TODO
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    String(String),
    Int(i64),
    MerkleTree(MerkleTree),
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_string())
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::Int(v)
    }
}

impl From<&Value> for middleware::Value {
    fn from(v: &Value) -> Self {
        match v {
            Value::String(s) => middleware::Value(hash_str(s).0),
            Value::Int(v) => middleware::Value::from(*v),
            // TODO
            Value::MerkleTree(mt) => middleware::Value([
                F::from_canonical_u64(mt.root as u64),
                F::ZERO,
                F::ZERO,
                F::ZERO,
            ]),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Int(v) => write!(f, "{}", v),
            Value::MerkleTree(mt) => write!(f, "mt:{}", mt.root),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignedPodBuilder {
    pub params: Params,
    pub kvs: HashMap<String, Value>,
}

impl SignedPodBuilder {
    pub fn new(params: &Params) -> Self {
        Self {
            params: params.clone(),
            kvs: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key: impl Into<String>, value: impl Into<Value>) {
        self.kvs.insert(key.into(), value.into());
    }

    pub fn sign<S: PodSigner>(&self, signer: &mut S) -> Result<SignedPod> {
        let mut kvs = HashMap::new();
        let mut key_string_map = HashMap::new();
        for (k, v) in self.kvs.iter() {
            let k_hash = hash_str(k);
            kvs.insert(k_hash, middleware::Value::from(v));
            key_string_map.insert(k_hash, k.clone());
        }
        let pod = signer.sign(&self.params, &kvs)?;
        Ok(SignedPod {
            pod,
            key_string_map,
        })
    }
}

/// SignedPod is a wrapper on top of backend::SignedPod, which additionally stores the
/// string<-->hash relation of the keys.
#[derive(Debug, Clone)]
pub struct SignedPod {
    pub pod: Box<dyn middleware::SignedPod>,
    /// HashMap to store the reverse relation between key strings and key hashes
    pub key_string_map: HashMap<Hash, String>,
}

impl SignedPod {
    pub fn id(&self) -> PodId {
        self.pod.id()
    }
    pub fn origin(&self) -> Origin {
        Origin(PodClass::Signed, self.id())
    }
    pub fn verify(&self) -> bool {
        self.pod.verify()
    }
    pub fn kvs(&self) -> HashMap<Hash, middleware::Value> {
        self.pod.kvs()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AnchoredKey(pub Origin, pub String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(r) => write!(f, "{}.{}", r.0 .1, r.1),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub NativeStatement, pub Vec<StatementArg>);

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationArg {
    Statement(Statement),
    Key(AnchoredKey),
    Literal(Value),
    Entry(String, Value),
}

impl From<Value> for OperationArg {
    fn from(v: Value) -> Self {
        Self::Literal(v)
    }
}

impl From<&Value> for OperationArg {
    fn from(v: &Value) -> Self {
        Self::Literal(v.clone())
    }
}

impl From<&str> for OperationArg {
    fn from(s: &str) -> Self {
        Self::Literal(Value::from(s))
    }
}

impl From<i64> for OperationArg {
    fn from(v: i64) -> Self {
        Self::Literal(Value::from(v))
    }
}

impl From<(Origin, &str)> for OperationArg {
    fn from((origin, key): (Origin, &str)) -> Self {
        Self::Key(AnchoredKey(origin, key.to_string()))
    }
}

impl From<(&SignedPod, &str)> for OperationArg {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        Self::Key(AnchoredKey(pod.origin(), key.to_string()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation(pub NativeOperation, pub Vec<OperationArg>);

#[derive(Debug)]
pub struct MainPodBuilder {
    pub params: Params,
    pub input_signed_pods: Vec<SignedPod>,
    pub input_main_pods: Vec<MainPod>,
    pub statements: Vec<Statement>,
    pub operations: Vec<Operation>,
    // Internal state
    const_cnt: usize,
}

impl MainPodBuilder {
    pub fn new(params: &Params) -> Self {
        Self {
            params: params.clone(),
            input_signed_pods: Vec::new(),
            input_main_pods: Vec::new(),
            statements: Vec::new(),
            operations: Vec::new(),
            const_cnt: 0,
        }
    }
    pub fn add_signed_pod(&mut self, pod: &SignedPod) {
        self.input_signed_pods.push(pod.clone());
    }
    pub fn add_main_pod(&mut self, pod: MainPod) {
        self.input_main_pods.push(pod);
    }
    pub fn insert(&mut self, st_op: (Statement, Operation)) {
        let (st, op) = st_op;
        self.statements.push(st);
        self.operations.push(op);
    }

    /// Convert [OperationArg]s to [StatementArg]s for the operations that work with entries
    fn op_args_entries(&mut self, args: &mut [OperationArg]) -> Vec<StatementArg> {
        let mut st_args = Vec::new();
        for arg in args.iter_mut() {
            match arg {
                OperationArg::Statement(_s) => panic!("can't convert Statement to StatementArg"),
                OperationArg::Key(k) => st_args.push(StatementArg::Key(k.clone())),
                OperationArg::Literal(v) => {
                    let k = format!("c{}", self.const_cnt);
                    self.const_cnt += 1;
                    let value_of_st = self.op(Operation(
                        NativeOperation::NewEntry,
                        vec![OperationArg::Entry(k.clone(), v.clone())],
                    ));
                    *arg = OperationArg::Key(AnchoredKey(Origin(PodClass::Main, SELF), k.clone()));
                    st_args.push(value_of_st.1[0].clone())
                }
                OperationArg::Entry(k, v) => {
                    st_args.push(StatementArg::Key(AnchoredKey(
                        Origin(PodClass::Main, SELF),
                        k.clone(),
                    )));
                    st_args.push(StatementArg::Literal(v.clone()))
                }
            };
        }
        st_args
    }

    pub fn op(&mut self, mut op: Operation) -> &Statement {
        use NativeOperation::*;
        let Operation(op_type, ref mut args) = op;
        // TODO: argument type checking
        let st = match op_type {
            None => Statement(NativeStatement::None, vec![]),
            NewEntry => Statement(NativeStatement::ValueOf, self.op_args_entries(args)),
            CopyStatement => todo!(),
            EqualFromEntries => Statement(NativeStatement::Equal, self.op_args_entries(args)),
            NotEqualFromEntries => Statement(NativeStatement::NotEqual, self.op_args_entries(args)),
            GtFromEntries => Statement(NativeStatement::Gt, self.op_args_entries(args)),
            LtFromEntries => Statement(NativeStatement::Lt, self.op_args_entries(args)),
            TransitiveEqualFromStatements => todo!(),
            GtToNotEqual => todo!(),
            LtToNotEqual => todo!(),
            ContainsFromEntries => Statement(NativeStatement::Contains, self.op_args_entries(args)),
            NotContainsFromEntries => {
                Statement(NativeStatement::NotContains, self.op_args_entries(args))
            }
            RenameContainedBy => todo!(),
            SumOf => todo!(),
            ProductOf => todo!(),
            MaxOf => todo!(),
        };
        self.operations.push(op);
        self.statements.push(st);
        &self.statements[self.statements.len() - 1]
    }

    pub fn prove<P: PodProver>(&self, prover: &mut P) -> Result<MainPod> {
        let compiler = MainPodCompiler::new(&self.params);
        let inputs = MainPodCompilerInputs {
            // signed_pods: &self.input_signed_pods,
            // main_pods: &self.input_main_pods,
            statements: &self.statements,
            operations: &self.operations,
        };
        // TODO: Error handling
        let (statements, operations) = compiler.compile(inputs).expect("TODO");

        let inputs = MainPodInputs {
            signed_pods: &self
                .input_signed_pods
                .iter()
                .map(|p| p.pod.as_ref())
                .collect_vec(),
            main_pods: &self
                .input_main_pods
                .iter()
                .map(|p| p.pod.as_ref())
                .collect_vec(),
            statements: &statements,
            operations: &operations,
        };
        let pod = prover.prove(&self.params, inputs)?;
        Ok(MainPod { pod })
    }
}

#[derive(Debug)]
pub struct MainPod {
    pub pod: Box<dyn middleware::MainPod>,
    // TODO: metadata
}

impl MainPod {
    pub fn id(&self) -> PodId {
        self.pod.id()
    }
    pub fn origin(&self) -> Origin {
        Origin(PodClass::Signed, self.id())
    }
}

struct MainPodCompilerInputs<'a> {
    // pub signed_pods: &'a [Box<dyn middleware::SignedPod>],
    // pub main_pods: &'a [Box<dyn middleware::MainPod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
}

struct MainPodCompiler {
    params: Params,
    // Output
    statements: Vec<middleware::Statement>,
    operations: Vec<middleware::Operation>,
}

impl MainPodCompiler {
    fn new(params: &Params) -> Self {
        Self {
            params: params.clone(),
            statements: Vec::new(),
            operations: Vec::new(),
        }
    }

    fn push_st_op(&mut self, st: middleware::Statement, op: middleware::Operation) {
        self.statements.push(st);
        self.operations.push(op);
    }

    fn compile_op_arg(&self, op_arg: &OperationArg) -> middleware::OperationArg {
        match op_arg {
            OperationArg::Statement(s) => middleware::OperationArg::Statement(self.compile_st(s)),
            OperationArg::Key(k) => middleware::OperationArg::Key(Self::compile_anchored_key(k)),
            OperationArg::Literal(_v) => {
                // OperationArg::Literal is a syntax sugar for the frontend.  This is translated to
                // a new ValueOf statement and it's key used instead.
                unreachable!()
            }
            OperationArg::Entry(_k, _v) => {
                // OperationArg::Entry is only used in the frontend.  The (key, value) will only
                // appear in the ValueOf statement in the backend.  This is because a new ValueOf
                // statement doesn't have any requirement on the key and value.
                middleware::OperationArg::None
            }
        }
    }

    fn compile_anchored_key(key: &AnchoredKey) -> middleware::AnchoredKey {
        middleware::AnchoredKey(key.0 .1, hash_str(&key.1))
    }

    fn compile_st(&self, st: &Statement) -> middleware::Statement {
        let mut st_args = Vec::new();
        let Statement(front_st_typ, front_st_args) = st;
        for front_st_arg in front_st_args {
            match front_st_arg {
                StatementArg::Literal(v) => {
                    st_args.push(middleware::StatementArg::Literal(middleware::Value::from(
                        v,
                    )));
                }
                StatementArg::Key(k) => {
                    let key = Self::compile_anchored_key(k);
                    st_args.push(middleware::StatementArg::Key(key));
                }
            };
            if st_args.len() > self.params.max_statement_args {
                panic!("too many statement st_args");
            }
        }

        middleware::Statement(*front_st_typ, st_args)
    }

    fn compile_st_op(&mut self, st: &Statement, op: &Operation) {
        let middle_st = self.compile_st(st);
        self.push_st_op(
            middle_st,
            middleware::Operation(
                op.0,
                op.1.iter().map(|arg| self.compile_op_arg(arg)).collect(),
            ),
        );
    }

    pub fn compile<'a>(
        mut self,
        inputs: MainPodCompilerInputs<'a>,
    ) -> Result<(Vec<middleware::Statement>, Vec<middleware::Operation>)> {
        let MainPodCompilerInputs {
            // signed_pods: _,
            // main_pods: _,
            statements,
            operations,
        } = inputs;
        for (st, op) in statements.iter().zip_eq(operations.iter()) {
            self.compile_st_op(st, op);
            if self.statements.len() > self.params.max_statements {
                panic!("too many statements");
            }
        }
        Ok((self.statements, self.operations))
    }
}

pub struct Printer {}

impl Printer {
    pub fn fmt_op_arg(&self, w: &mut dyn Write, arg: &OperationArg) -> io::Result<()> {
        match arg {
            OperationArg::Statement(s) => write!(w, "{}", s),
            OperationArg::Key(k) => write!(w, "{}.{}", k.0 .1, k.1),
            OperationArg::Literal(v) => write!(w, "{}", v),
            OperationArg::Entry(k, v) => write!(w, "({}, {})", k, v),
        }
    }

    pub fn fmt_op(&self, w: &mut dyn Write, op: &Operation) -> io::Result<()> {
        write!(w, "{:?} ", op.0)?;
        for (i, arg) in op.1.iter().enumerate() {
            if i != 0 {
                write!(w, " ")?;
            }
            self.fmt_op_arg(w, arg)?;
        }
        Ok(())
    }

    // TODO fn fmt_signed_pod_builder

    pub fn fmt_signed_pod(&self, w: &mut dyn Write, pod: &SignedPod) -> io::Result<()> {
        writeln!(w, "SignedPod (id:{}):", pod.id())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in pod.pod.kvs().iter().sorted_by_key(|kv| kv.0) {
            writeln!(w, "  - {}: {}", k, v)?;
        }
        Ok(())
    }

    pub fn fmt_main_pod_builder(&self, w: &mut dyn Write, pod: &MainPodBuilder) -> io::Result<()> {
        writeln!(w, "MainPod:")?;
        writeln!(w, "  input_signed_pods:")?;
        for in_pod in &pod.input_signed_pods {
            writeln!(w, "    - {}", in_pod.id())?;
        }
        writeln!(w, "  input_main_pods:")?;
        for in_pod in &pod.input_main_pods {
            writeln!(w, "    - {}", in_pod.id())?;
        }
        writeln!(w, "  statements:")?;
        for (st, op) in pod.statements.iter().zip_eq(pod.operations.iter()) {
            write!(w, "    - {} <- ", st)?;
            self.fmt_op(w, op)?;
            write!(w, "\n")?;
        }
        Ok(())
    }

    // TODO fn fmt_main_pod
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::mock_signed::MockSigner;
    use std::io;

    macro_rules! args {
        ($($arg:expr),+) => {vec![$(OperationArg::from($arg)),*]}
    }

    macro_rules! op {
        (eq, $($arg:expr),+) => { Operation(NativeOperation::EqualFromEntries, args!($($arg),*)) };
        (ne, $($arg:expr),+) => { Operation(NativeOperation::NotEqualFromEntries, args!($($arg),*)) };
        (gt, $($arg:expr),+) => { Operation(NativeOperation::GtFromEntries, args!($($arg),*)) };
        (lt, $($arg:expr),+) => { Operation(NativeOperation::LtFromEntries, args!($($arg),*)) };
        (contains, $($arg:expr),+) => { Operation(NativeOperation::ContainsFromEntries, args!($($arg),*)) };
        (not_contains, $($arg:expr),+) => { Operation(NativeOperation::NotContainsFromEntries, args!($($arg),*)) };
    }

    pub fn zu_kyc_sign_pod_builders(params: &Params) -> (SignedPodBuilder, SignedPodBuilder) {
        let mut gov_id = SignedPodBuilder::new(params);
        gov_id.insert("idNumber", "4242424242");
        gov_id.insert("dateOfBirth", 1169909384);
        gov_id.insert("socialSecurityNumber", "G2121210");

        let mut pay_stub = SignedPodBuilder::new(params);
        pay_stub.insert("socialSecurityNumber", "G2121210");
        pay_stub.insert("startDate", 1706367566);

        (gov_id, pay_stub)
    }

    pub fn zu_kyc_pod_builder(
        params: &Params,
        gov_id: &SignedPod,
        pay_stub: &SignedPod,
    ) -> MainPodBuilder {
        let sanction_list = Value::MerkleTree(MerkleTree { root: 1 });
        let now_minus_18y: i64 = 1169909388;
        let now_minus_1y: i64 = 1706367566;

        let mut kyc = MainPodBuilder::new(&params);
        kyc.add_signed_pod(&gov_id);
        kyc.add_signed_pod(&pay_stub);
        kyc.op(op!(not_contains, &sanction_list, (gov_id, "idNumber")));
        kyc.op(op!(lt, (gov_id, "dateOfBirth"), now_minus_18y));
        kyc.op(op!(
            eq,
            (gov_id, "socialSecurityNumber"),
            (pay_stub, "socialSecurityNumber")
        ));
        kyc.op(op!(eq, (pay_stub, "startDate"), now_minus_1y));

        kyc
    }

    #[test]
    fn test_front_0() -> Result<()> {
        let printer = Printer {};
        let mut w = io::stdout();

        let params = Params::default();
        let (gov_id, pay_stub) = zu_kyc_sign_pod_builders(&params);

        // TODO: print pods from the builder

        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id = gov_id.sign(&mut signer).unwrap();
        printer.fmt_signed_pod(&mut w, &gov_id).unwrap();

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer).unwrap();
        printer.fmt_signed_pod(&mut w, &pay_stub).unwrap();

        let kyc = zu_kyc_pod_builder(&params, &gov_id, &pay_stub);
        printer.fmt_main_pod_builder(&mut w, &kyc).unwrap();

        // TODO: prove kyc with MockProver and print it

        Ok(())
    }
}
