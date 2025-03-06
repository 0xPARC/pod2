//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use anyhow::{anyhow, Result};
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::From;
use std::{fmt, hash as h};

use crate::middleware::{
    self,
    containers::{Array, Dictionary, Set},
    hash_str, Hash, MainPodInputs, NativeOperation, NativePredicate, Params, PodId, PodProver,
    PodSigner, SELF,
};
use crate::middleware::{OperationType, Predicate, KEY_SIGNER, KEY_TYPE};

mod custom;
mod operation;
mod statement;
pub use custom::*;
pub use operation::*;
pub use statement::*;

/// This type is just for presentation purposes.
#[derive(Clone, Debug, Default, h::Hash, PartialEq, Eq)]
pub enum PodClass {
    #[default]
    Signed,
    Main,
}

// An Origin, which represents a reference to an ancestor POD.
#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Default)]
pub struct Origin(pub PodClass, pub PodId);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    String(String),
    Int(i64),
    Bool(bool),
    Dictionary(Dictionary),
    Set(Set),
    Array(Array),
    Raw(middleware::Value),
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

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<&Value> for middleware::Value {
    fn from(v: &Value) -> Self {
        match v {
            Value::String(s) => hash_str(s).value(),
            Value::Int(v) => middleware::Value::from(*v),
            Value::Bool(b) => middleware::Value::from(*b as i64),
            Value::Dictionary(d) => d.commitment().value(),
            Value::Set(s) => s.commitment().value(),
            Value::Array(a) => a.commitment().value(),
            Value::Raw(v) => *v,
        }
    }
}

impl From<middleware::Value> for Value {
    fn from(v: middleware::Value) -> Self {
        Self::Raw(v)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Int(v) => write!(f, "{}", v),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Dictionary(d) => write!(f, "dict:{}", d.commitment()),
            Value::Set(s) => write!(f, "set:{}", s.commitment()),
            Value::Array(a) => write!(f, "arr:{}", a.commitment()),
            Value::Raw(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignedPodBuilder {
    pub params: Params,
    pub kvs: HashMap<String, Value>,
}

impl fmt::Display for SignedPodBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPodBuilder:")?;
        for (k, v) in self.kvs.iter().sorted_by_key(|kv| kv.0) {
            writeln!(f, "  - {}: {}", k, v)?;
        }
        Ok(())
    }
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
        // Sign POD with committed KV store.
        let committed_kvs = self
            .kvs
            .iter()
            .map(|(k, v)| (hash_str(k), v.into()))
            .collect::<HashMap<_, _>>();
        let pod = signer.sign(&self.params, &committed_kvs)?;

        let mut kvs = self.kvs.clone();

        // Type and signer information are passed in by the
        // backend. Include these in the frontend representation.
        let mid_kvs = pod.kvs();
        let pod_type = mid_kvs
            .get(&crate::middleware::AnchoredKey(
                pod.id(),
                hash_str(KEY_TYPE),
            ))
            .cloned()
            .ok_or(anyhow!("Missing POD type information in POD: {:?}", pod))?;
        let pod_signer = mid_kvs
            .get(&crate::middleware::AnchoredKey(
                pod.id(),
                hash_str(KEY_SIGNER),
            ))
            .cloned()
            .ok_or(anyhow!("Missing POD signer in POD: {:?}", pod))?;
        kvs.insert(KEY_TYPE.to_string(), pod_type.into());
        kvs.insert(KEY_SIGNER.to_string(), pod_signer.into());
        Ok(SignedPod { pod, kvs })
    }
}

/// SignedPod is a wrapper on top of backend::SignedPod, which additionally stores the
/// string<-->hash relation of the keys.
#[derive(Debug, Clone)]
pub struct SignedPod {
    pub pod: Box<dyn middleware::Pod>,
    /// Key-value pairs as represented in the frontend. These should
    /// correspond to the entries of `pod.kvs()` after hashing and
    /// replacing each key with its corresponding anchored key.
    pub kvs: HashMap<String, Value>,
}

impl fmt::Display for SignedPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPod (id:{}):", self.id())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in self.kvs.iter().sorted_by_key(|kv| kv.0) {
            writeln!(
                f,
                "  - {} = {}: {}",
                hash_str(k),
                k,
                crate::middleware::Value::from(v)
            )?;
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
        self.pod
            .kvs()
            .into_iter()
            .map(|(middleware::AnchoredKey(_, k), v)| (k, v))
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, h::Hash)]
pub struct AnchoredKey(pub Origin, pub String);

impl From<AnchoredKey> for middleware::AnchoredKey {
    fn from(ak: AnchoredKey) -> Self {
        middleware::AnchoredKey(ak.0 .1, hash_str(&ak.1))
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
    key_table: HashMap<Hash, String>,
    pod_class_table: HashMap<PodId, PodClass>,
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
            writeln!(f)?;
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
            key_table: HashMap::new(),
            pod_class_table: HashMap::from_iter([(SELF, PodClass::Main)]),
        }
    }
    pub fn add_signed_pod(&mut self, pod: &SignedPod) {
        self.input_signed_pods.push(pod.clone());
        // Add key-hash correspondences to key table.
        pod.kvs.iter().for_each(|(key, _)| {
            self.key_table.insert(hash_str(key), key.clone());
        });
        // Add POD class to POD class table.
        self.pod_class_table.insert(pod.id(), PodClass::Signed);
    }
    pub fn add_main_pod(&mut self, pod: MainPod) {
        // Add POD class to POD class table.
        self.pod_class_table.insert(pod.id(), PodClass::Main);
        // Add key-hash and POD ID-class correspondences to tables.
        pod.public_statements
            .iter()
            .flat_map(|s| &s.1)
            .flat_map(|arg| match arg {
                StatementArg::Key(AnchoredKey(Origin(pod_class, pod_id), key)) => {
                    Some((*pod_id, pod_class.clone(), hash_str(key), key.clone()))
                }
                _ => None,
            })
            .for_each(|(pod_id, pod_class, hash, key)| {
                self.pod_class_table.insert(pod_id, pod_class);
                self.key_table.insert(hash, key);
            });
        self.input_main_pods.push(pod);
    }
    pub fn insert(&mut self, st_op: (Statement, Operation)) {
        let (st, op) = st_op;
        self.statements.push(st);
        self.operations.push(op);
    }

    /// Convert [OperationArg]s to [StatementArg]s for the operations that work with entries
    fn op_args_entries(
        &mut self,
        public: bool,
        args: &mut [OperationArg],
    ) -> Result<Vec<StatementArg>> {
        let mut st_args = Vec::new();
        for arg in args.iter_mut() {
            match arg {
                OperationArg::Statement(s) => {
                    if s.0 == Predicate::Native(NativePredicate::ValueOf) {
                        st_args.push(s.1[0].clone())
                    } else {
                        panic!("Invalid statement argument.");
                    }
                }
                OperationArg::Literal(v) => {
                    let k = format!("c{}", self.const_cnt);
                    self.const_cnt += 1;
                    let value_of_st = self.op(
                        public,
                        Operation(
                            OperationType::Native(NativeOperation::NewEntry),
                            vec![OperationArg::Entry(k.clone(), v.clone())],
                        ),
                    )?;
                    *arg = OperationArg::Statement(value_of_st.clone());
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
        Ok(st_args)
    }

    pub fn pub_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(true, op)
    }

    pub fn priv_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(false, op)
    }

    fn op(&mut self, public: bool, mut op: Operation) -> Result<Statement> {
        use NativeOperation::*;
        let Operation(op_type, ref mut args) = &mut op;
        // TODO: argument type checking
        let st = match op_type {
            OperationType::Native(o) => match o {
                None => Statement(Predicate::Native(NativePredicate::None), vec![]),
                NewEntry => Statement(
                    Predicate::Native(NativePredicate::ValueOf),
                    self.op_args_entries(public, args)?,
                ),
                CopyStatement => todo!(),
                EqualFromEntries => Statement(
                    Predicate::Native(NativePredicate::Equal),
                    self.op_args_entries(public, args)?,
                ),
                NotEqualFromEntries => Statement(
                    Predicate::Native(NativePredicate::NotEqual),
                    self.op_args_entries(public, args)?,
                ),
                GtFromEntries => Statement(
                    Predicate::Native(NativePredicate::Gt),
                    self.op_args_entries(public, args)?,
                ),
                LtFromEntries => Statement(
                    Predicate::Native(NativePredicate::Lt),
                    self.op_args_entries(public, args)?,
                ),
                TransitiveEqualFromStatements => todo!(),
                GtToNotEqual => todo!(),
                LtToNotEqual => todo!(),
                ContainsFromEntries => Statement(
                    Predicate::Native(NativePredicate::Contains),
                    self.op_args_entries(public, args)?,
                ),
                NotContainsFromEntries => Statement(
                    Predicate::Native(NativePredicate::NotContains),
                    self.op_args_entries(public, args)?,
                ),
                RenameContainedBy => todo!(),
                SumOf => todo!(),
                ProductOf => todo!(),
                MaxOf => todo!(),
            },
            OperationType::Custom(cpr) => {
                // All args should be statements to be pattern matched against statement templates.
                let args = args.iter().map(
                    |a| match a {
                        OperationArg::Statement(s) => middleware::Statement::try_from(s.clone()),
                            _ => Err(anyhow!("Invalid argument {} to operation corresponding to custom predicate {:?}.", a, cpr))
                    }
                ).collect::<Result<Vec<_>>>()?;
                // Match these statements against the custom predicate definition
                let bindings = cpr.match_against(&args)?;
                let output_arg_values = (0..cpr.arg_len())
                    .map(|i| {
                        bindings.get(&i).cloned().ok_or(anyhow!(
                            "Wildcard {} of custom predicate {:?} is unbound.",
                            i,
                            cpr
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let output_args = output_arg_values
                    .chunks(2)
                    .map(|chunk| {
                        Ok(StatementArg::Key(AnchoredKey(
                            Origin(
                                self.pod_class_table
                                    .get(&PodId(chunk[0].into()))
                                    .cloned()
                                    .ok_or(anyhow!("Missing POD class value."))?,
                                PodId(chunk[0].into()),
                            ),
                            self.key_table
                                .get(&chunk[1].into())
                                .cloned()
                                .ok_or(anyhow!("Missing key corresponding to hash."))?,
                        )))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Statement(Predicate::Custom(cpr.clone()), output_args)
            }
        };
        self.operations.push(op);
        if public {
            self.public_statements.push(st.clone());
        }

        // Add key-hash pairs in statement to table.
        st.1.iter().for_each(|arg| {
            if let StatementArg::Key(AnchoredKey(_, key)) = arg {
                self.key_table.insert(hash_str(key), key.clone());
            }
        });

        self.statements.push(st);
        Ok(self.statements[self.statements.len() - 1].clone())
    }

    pub fn reveal(&mut self, st: &Statement) {
        self.public_statements.push(st.clone());
    }

    pub fn prove<P: PodProver>(&self, prover: &mut P, params: &Params) -> Result<MainPod> {
        let compiler = MainPodCompiler::new(&self.params);
        let inputs = MainPodCompilerInputs {
            // signed_pods: &self.input_signed_pods,
            // main_pods: &self.input_main_pods,
            statements: &self.statements,
            operations: &self.operations,
            public_statements: &self.public_statements,
        };

        let (statements, operations, public_statements) = compiler.compile(inputs, params)?;
        let inputs = MainPodInputs {
            signed_pods: &self.input_signed_pods.iter().map(|p| &p.pod).collect_vec(),
            main_pods: &self.input_main_pods.iter().map(|p| &p.pod).collect_vec(),
            statements: &statements,
            operations: &operations,
            public_statements: &public_statements,
        };
        let pod = prover.prove(&self.params, inputs)?;

        // Gather public statements, making sure to inject the type
        // information specified by the backend.
        let pod_id = pod.id();
        let type_key_hash = hash_str(KEY_TYPE);
        let type_statement = pod
            .pub_statements()
            .into_iter()
            .find_map(|s| match s {
                crate::middleware::Statement::ValueOf(
                    crate::middleware::AnchoredKey(id, key),
                    value,
                ) if id == pod_id && key == type_key_hash => Some(Statement(
                    Predicate::Native(NativePredicate::ValueOf),
                    vec![
                        StatementArg::Key(AnchoredKey(
                            Origin(PodClass::Main, pod_id),
                            KEY_TYPE.to_string(),
                        )),
                        StatementArg::Literal(value.into()),
                    ],
                )),
                _ => None,
            })
            .ok_or(anyhow!("Missing POD type information in POD: {:?}", pod))?;
        // Replace instances of `SELF` with the POD ID for consistency
        // with `pub_statements` method.
        let public_statements = [type_statement]
            .into_iter()
            .chain(self.public_statements.clone().into_iter().map(|s| {
                let s_type = s.0;
                let s_args = s
                    .1
                    .into_iter()
                    .map(|arg| match arg {
                        StatementArg::Key(AnchoredKey(Origin(class, id), key)) if id == SELF => {
                            StatementArg::Key(AnchoredKey(Origin(class, pod_id), key))
                        }
                        _ => arg,
                    })
                    .collect();
                Statement(s_type, s_args)
            }))
            .collect();

        Ok(MainPod {
            pod,
            public_statements,
        })
    }
}

#[derive(Debug)]
pub struct MainPod {
    pub pod: Box<dyn middleware::Pod>,
    pub public_statements: Vec<Statement>,
}

impl fmt::Display for MainPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MainPod: {}", self.pod.id())?;
        writeln!(f, "  valid?  {}", self.pod.verify())?;
        writeln!(f, "  statements:")?;
        for st in &self.pod.pub_statements() {
            writeln!(f, "    - {}", st)?;
        }
        writeln!(f, "  kvs:")?;
        for (k, v) in &self.pod.kvs() {
            writeln!(f, "    - {}: {}", k, v)?;
        }
        Ok(())
    }
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

    fn compile_op_arg(&self, op_arg: &OperationArg) -> Option<middleware::Statement> {
        match op_arg {
            OperationArg::Statement(s) => self.compile_st(s).ok(),
            OperationArg::Literal(_v) => {
                // OperationArg::Literal is a syntax sugar for the frontend.  This is translated to
                // a new ValueOf statement and it's key used instead.
                unreachable!()
            }
            OperationArg::Entry(_k, _v) => {
                // OperationArg::Entry is only used in the frontend.  The (key, value) will only
                // appear in the ValueOf statement in the backend.  This is because a new ValueOf
                // statement doesn't have any requirement on the key and value.
                None
            }
        }
    }

    fn compile_st(&self, st: &Statement) -> Result<middleware::Statement> {
        st.clone().try_into()
    }

    fn compile_op(&self, op: &Operation) -> Result<middleware::Operation> {
        // TODO
        let mop_code: OperationType = op.0.clone();
        let mop_args =
            op.1.iter()
                .flat_map(|arg| self.compile_op_arg(arg).map(|s| Ok(s.try_into()?)))
                .collect::<Result<Vec<middleware::Statement>>>()?;
        middleware::Operation::op(mop_code, &mop_args)
    }

    fn compile_st_op(&mut self, st: &Statement, op: &Operation, params: &Params) -> Result<()> {
        let middle_st = self.compile_st(st)?;
        let middle_op = self.compile_op(op)?;
        let is_correct = middle_op.check(params, &middle_st)?;
        if !is_correct {
            // todo: improve error handling
            Err(anyhow!(
                "Compile failed due to invalid deduction:\n {} ⇏ {}",
                middle_op,
                middle_st
            ))
        } else {
            self.push_st_op(middle_st, middle_op);
            Ok(())
        }
    }

    pub fn compile(
        mut self,
        inputs: MainPodCompilerInputs<'_>,
        params: &Params,
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
            self.compile_st_op(st, op, params)?;
            if self.statements.len() > self.params.max_statements {
                panic!("too many statements");
            }
        }
        let public_statements = public_statements
            .iter()
            .map(|st| self.compile_st(st))
            .collect::<Result<Vec<_>>>()?;
        Ok((self.statements, self.operations, public_statements))
    }
}

// TODO fn fmt_signed_pod_builder
// TODO fn fmt_main_pod

#[macro_use]
pub mod build_utils {
    #[macro_export]
    macro_rules! op_args {
        ($($arg:expr),+) => {vec![$($crate::frontend::OperationArg::from($arg)),*]}
    }

    #[macro_export]
    macro_rules! op {
        (eq, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::EqualFromEntries),
            $crate::op_args!($($arg),*)) };
        (ne, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native(crate::middleware::NativeOperation::NotEqualFromEntries),
            crate::op_args!($($arg),*)) };
        (gt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::GtFromEntries),
            crate::op_args!($($arg),*)) };
        (lt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::LtFromEntries),
            crate::op_args!($($arg),*)) };
        (contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::ContainsFromEntries),
            crate::op_args!($($arg),*)) };
        (not_contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::NotContainsFromEntries),
            crate::op_args!($($arg),*)) };
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::backends::plonky2::mock_main::MockProver;
    use crate::backends::plonky2::mock_signed::MockSigner;
    use crate::examples::{
        eth_dos_pod_builder, eth_friend_signed_pod_builder, great_boy_pod_full_flow,
        tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_sign_pod_builders,
    };

    // Check that frontend public statements agree with those
    // embedded in a MainPod.
    fn check_public_statements(pod: &MainPod) -> Result<()> {
        std::iter::zip(pod.public_statements.clone(), pod.pod.pub_statements()).try_for_each(
            |(fes, s)| crate::middleware::Statement::try_from(fes).map(|fes| assert_eq!(fes, s)),
        )
    }

    // Check that frontend key-values agree with those embedded in a
    // SignedPod.
    fn check_kvs(pod: &SignedPod) -> Result<()> {
        let kvs = pod
            .kvs
            .iter()
            .map(|(k, v)| (hash_str(k), middleware::Value::from(v)))
            .collect::<HashMap<_, _>>();
        let embedded_kvs = pod
            .pod
            .kvs()
            .into_iter()
            .map(|(middleware::AnchoredKey(_, k), v)| (k, v))
            .collect::<HashMap<_, _>>();

        if kvs == embedded_kvs {
            Ok(())
        } else {
            Err(anyhow!(
                "KVs {:?} do not agree with those embedded in the POD: {:?}",
                kvs,
                embedded_kvs
            ))
        }
    }

    #[test]
    fn test_front_zu_kyc() -> Result<()> {
        let params = Params::default();
        let (gov_id, pay_stub, sanction_list) = zu_kyc_sign_pod_builders(&params);

        println!("{}", gov_id);
        println!("{}", pay_stub);

        let mut signer = MockSigner {
            pk: "ZooGov".into(),
        };
        let gov_id = gov_id.sign(&mut signer)?;
        check_kvs(&gov_id)?;
        println!("{}", gov_id);

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer)?;
        check_kvs(&pay_stub)?;
        println!("{}", pay_stub);

        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list = sanction_list.sign(&mut signer)?;
        check_kvs(&sanction_list)?;
        println!("{}", sanction_list);

        let kyc_builder = zu_kyc_pod_builder(&params, &gov_id, &pay_stub, &sanction_list)?;
        println!("{}", kyc_builder);

        // prove kyc with MockProver and print it
        let mut prover = MockProver {};
        let kyc = kyc_builder.prove(&mut prover, &params)?;

        println!("{}", kyc);

        check_public_statements(&kyc)
    }

    #[test]
    fn test_ethdos() -> Result<()> {
        let params = Params::default();

        let mut alice = MockSigner { pk: "Alice".into() };
        let bob = MockSigner { pk: "Bob".into() };
        let mut charlie = MockSigner {
            pk: "Charlie".into(),
        };

        // Alice attests that she is ETH friends with Charlie and Charlie
        // attests that he is ETH friends with Bob.
        let alice_attestation =
            eth_friend_signed_pod_builder(&params, charlie.pubkey().into()).sign(&mut alice)?;
        check_kvs(&alice_attestation)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.pubkey().into()).sign(&mut charlie)?;
        check_kvs(&charlie_attestation)?;

        let mut prover = MockProver {};
        let alice_bob_ethdos = eth_dos_pod_builder(
            &params,
            &alice_attestation,
            &charlie_attestation,
            &bob.pubkey().into(),
        )?
        .prove(&mut prover, &params)?;

        check_public_statements(&alice_bob_ethdos)
    }

    #[test]
    fn test_front_great_boy() -> Result<()> {
        let great_boy = great_boy_pod_full_flow()?;
        println!("{}", great_boy);

        // TODO: prove great_boy with MockProver and print it

        Ok(())
    }

    #[test]
    fn test_front_tickets() -> Result<()> {
        let builder = tickets_pod_full_flow()?;
        println!("{}", builder);

        Ok(())
    }

    #[test]
    #[should_panic]
    fn test_false_st() {
        let params = Params::default();
        let mut builder = SignedPodBuilder::new(&params);

        builder.insert("num", 2);

        let mut signer = MockSigner {
            pk: "signer".into(),
        };
        let pod = builder.sign(&mut signer).unwrap();

        println!("{}", pod);

        let mut builder = MainPodBuilder::new(&params);
        builder.add_signed_pod(&pod);
        builder.pub_op(op!(gt, (&pod, "num"), 5)).unwrap();

        let mut prover = MockProver {};
        let false_pod = builder.prove(&mut prover, &params).unwrap();

        println!("{}", builder);
        println!("{}", false_pod);
    }
}
