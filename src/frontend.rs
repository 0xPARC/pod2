//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use anyhow::Result;
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::From;
use std::fmt;

use crate::middleware::{
    self,
    containers::{Array, Container, Dictionary, Set},
    hash_str, Hash, MainPodInputs, NativeOperation, NativeStatement, Params, PodId, PodProver,
    PodSigner, SELF,
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
pub enum Value {
    String(String),
    Int(i64),
    Dictionary(Dictionary),
    Set(Set),
    Array(Array),
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
            Value::Dictionary(d) => middleware::Value(d.cm().0),
            Value::Set(s) => middleware::Value(s.cm().0),
            Value::Array(a) => middleware::Value(a.cm().0),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Int(v) => write!(f, "{}", v),
            Value::Dictionary(d) => write!(f, "dict:{}", d.cm()),
            Value::Set(s) => write!(f, "set:{}", s.cm()),
            Value::Array(a) => write!(f, "arr:{}", a.cm()),
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

impl fmt::Display for SignedPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPod (id:{}):", self.id())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in self.pod.kvs().iter().sorted_by_key(|kv| kv.0) {
            writeln!(f, "  - {}: {}", k, v)?;
        }
        Ok(())
    }
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

impl fmt::Display for OperationArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationArg::Statement(s) => write!(f, "{}", s),
            OperationArg::Key(k) => write!(f, "{}.{}", k.0 .1, k.1),
            OperationArg::Literal(v) => write!(f, "{}", v),
            OperationArg::Entry(k, v) => write!(f, "({}, {})", k, v),
        }
    }
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

impl fmt::Display for Operation {
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

#[derive(Debug)]
pub struct MainPodBuilder {
    pub params: Params,
    pub input_signed_pods: Vec<SignedPod>,
    pub input_main_pods: Vec<MainPod>,
    pub statements: Vec<Statement>,
    pub operations: Vec<Operation>,
    pub public_statements: Vec<Statement>,
    // Internal state
    const_cnt: usize,
}

impl fmt::Display for MainPodBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MainPod:")?;
        writeln!(f, "  input_signed_pods:")?;
        for in_pod in &self.input_signed_pods {
            writeln!(f, "    - {}", in_pod.id())?;
        }
        writeln!(f, "  input_main_pods:")?;
        for in_pod in &self.input_main_pods {
            writeln!(f, "    - {}", in_pod.id())?;
        }
        writeln!(f, "  statements:")?;
        for (st, op) in self.statements.iter().zip_eq(self.operations.iter()) {
            write!(f, "    - {} <- ", st)?;
            write!(f, "{}", op)?;
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl MainPodBuilder {
    pub fn new(params: &Params) -> Self {
        Self {
            params: params.clone(),
            input_signed_pods: Vec::new(),
            input_main_pods: Vec::new(),
            statements: Vec::new(),
            operations: Vec::new(),
            public_statements: Vec::new(),
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
    fn op_args_entries(&mut self, public: bool, args: &mut [OperationArg]) -> Vec<StatementArg> {
        let mut st_args = Vec::new();
        for arg in args.iter_mut() {
            match arg {
                OperationArg::Statement(_s) => panic!("can't convert Statement to StatementArg"),
                OperationArg::Key(k) => st_args.push(StatementArg::Key(k.clone())),
                OperationArg::Literal(v) => {
                    let k = format!("c{}", self.const_cnt);
                    self.const_cnt += 1;
                    let value_of_st = self.op(
                        public,
                        Operation(
                            NativeOperation::NewEntry,
                            vec![OperationArg::Entry(k.clone(), v.clone())],
                        ),
                    );
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

    pub fn pub_op(&mut self, op: Operation) -> Statement {
        self.op(true, op)
    }

    pub fn op(&mut self, public: bool, mut op: Operation) -> Statement {
        use NativeOperation::*;
        let Operation(op_type, ref mut args) = op;
        // TODO: argument type checking
        let st = match op_type {
            None => Statement(NativeStatement::None, vec![]),
            NewEntry => Statement(NativeStatement::ValueOf, self.op_args_entries(public, args)),
            CopyStatement => todo!(),
            EqualFromEntries => {
                Statement(NativeStatement::Equal, self.op_args_entries(public, args))
            }
            NotEqualFromEntries => Statement(
                NativeStatement::NotEqual,
                self.op_args_entries(public, args),
            ),
            GtFromEntries => Statement(NativeStatement::Gt, self.op_args_entries(public, args)),
            LtFromEntries => Statement(NativeStatement::Lt, self.op_args_entries(public, args)),
            TransitiveEqualFromStatements => todo!(),
            GtToNotEqual => todo!(),
            LtToNotEqual => todo!(),
            ContainsFromEntries => Statement(
                NativeStatement::Contains,
                self.op_args_entries(public, args),
            ),
            NotContainsFromEntries => Statement(
                NativeStatement::NotContains,
                self.op_args_entries(public, args),
            ),
            RenameContainedBy => todo!(),
            SumOf => todo!(),
            ProductOf => todo!(),
            MaxOf => todo!(),
        };
        self.operations.push(op);
        if public {
            self.public_statements.push(st.clone());
        }
        self.statements.push(st);
        self.statements[self.statements.len() - 1].clone()
    }

    pub fn reveal(&mut self, st: &Statement) {
        self.public_statements.push(st.clone());
    }

    pub fn prove<P: PodProver>(&self, prover: &mut P) -> Result<MainPod> {
        let compiler = MainPodCompiler::new(&self.params);
        let inputs = MainPodCompilerInputs {
            // signed_pods: &self.input_signed_pods,
            // main_pods: &self.input_main_pods,
            statements: &self.statements,
            operations: &self.operations,
            public_statements: &self.public_statements,
        };
        let (statements, operations, public_statements) = compiler.compile(inputs)?;

        let inputs = MainPodInputs {
            signed_pods: &self.input_signed_pods.iter().map(|p| &p.pod).collect_vec(),
            main_pods: &self.input_main_pods.iter().map(|p| &p.pod).collect_vec(),
            statements: &statements,
            operations: &operations,
            public_statements: &public_statements,
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
        Origin(PodClass::Main, self.id())
    }
}

struct MainPodCompilerInputs<'a> {
    // pub signed_pods: &'a [Box<dyn middleware::SignedPod>],
    // pub main_pods: &'a [Box<dyn middleware::MainPod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    pub public_statements: &'a [Statement],
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
    ) -> Result<(
        Vec<middleware::Statement>, // input statements
        Vec<middleware::Operation>,
        Vec<middleware::Statement>, // public statements
    )> {
        let MainPodCompilerInputs {
            // signed_pods: _,
            // main_pods: _,
            statements,
            operations,
            public_statements,
        } = inputs;
        for (st, op) in statements.iter().zip_eq(operations.iter()) {
            self.compile_st_op(st, op);
            if self.statements.len() > self.params.max_statements {
                panic!("too many statements");
            }
        }
        let public_statements = public_statements
            .iter()
            .map(|st| self.compile_st(st))
            .collect_vec();
        Ok((self.statements, self.operations, public_statements))
    }
}

// TODO fn fmt_signed_pod_builder
// TODO fn fmt_main_pod

#[macro_use]
pub mod build_utils {
    #[macro_export]
    macro_rules! op_args {
        ($($arg:expr),+) => {vec![$(crate::frontend::OperationArg::from($arg)),*]}
    }

    #[macro_export]
    macro_rules! op {
        (eq, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::EqualFromEntries,
            crate::op_args!($($arg),*)) };
        (ne, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::NotEqualFromEntries,
            crate::op_args!($($arg),*)) };
        (gt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::GtFromEntries,
            crate::op_args!($($arg),*)) };
        (lt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::LtFromEntries,
            crate::op_args!($($arg),*)) };
        (contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::ContainsFromEntries,
            crate::op_args!($($arg),*)) };
        (not_contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::NativeOperation::NotContainsFromEntries,
            crate::op_args!($($arg),*)) };
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::mock_signed::MockSigner;
    use crate::examples::{great_boy_pod_full_flow, zu_kyc_pod_builder, zu_kyc_sign_pod_builders};

    #[test]
    fn test_front_zu_kyc() -> Result<()> {
        let params = Params::default();
        let (gov_id, pay_stub) = zu_kyc_sign_pod_builders(&params);

        // TODO: print pods from the builder

        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id = gov_id.sign(&mut signer).unwrap();
        println!("{}", gov_id);

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer).unwrap();
        println!("{}", pay_stub);

        let kyc = zu_kyc_pod_builder(&params, &gov_id, &pay_stub);
        println!("{}", kyc);

        // TODO: prove kyc with MockProver and print it

        Ok(())
    }

    #[test]
    fn test_front_great_boy() -> Result<()> {
        let great_boy = great_boy_pod_full_flow();
        println!("{}", great_boy);

        // TODO: prove kyc with MockProver and print it

        Ok(())
    }
}
