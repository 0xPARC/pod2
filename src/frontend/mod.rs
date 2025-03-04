//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use anyhow::{anyhow, Error, Result};
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::From;
use std::sync::Arc;
use std::{fmt, hash as h};

use crate::middleware::{
    self,
    containers::{Array, Dictionary, Set},
    hash_str, Hash, MainPodInputs, NativeOperation, NativePredicate, Params, PodId, PodProver,
    PodSigner, SELF,
};
use crate::middleware::{OperationType, Predicate, KEY_SIGNER};

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
            Value::Raw(v) => v.clone(),
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
        let mut kvs = HashMap::new();
        let mut key_string_map = HashMap::new();
        let mut value_hash_map = HashMap::new();
        for (k, v) in self.kvs.iter() {
            let k_hash = hash_str(k);
            let v_hash = middleware::Value::from(v);
            kvs.insert(k_hash, v_hash);
            key_string_map.insert(k_hash, k.clone());
            value_hash_map.insert(v_hash.into(), v.clone());
        }
        let pod = signer.sign(&self.params, &kvs)?;
        Ok(SignedPod {
            pod,
            key_string_map,
            value_hash_map,
        })
    }
}

/// SignedPod is a wrapper on top of backend::SignedPod, which additionally stores the
/// string<-->hash relation of the keys.
#[derive(Debug, Clone)]
pub struct SignedPod {
    pub pod: Box<dyn middleware::Pod>,
    /// HashMap to store the reverse relation between key strings and key hashes
    pub key_string_map: HashMap<Hash, String>,
    /// HashMap to store the reverse relation between values and their hashes
    pub value_hash_map: HashMap<Hash, Value>,
}

impl fmt::Display for SignedPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPod (id:{}):", self.id())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in self.kvs().iter().sorted_by_key(|kv| kv.0) {
            writeln!(
                f,
                "  - {} = {}: {}",
                k,
                *self.key_string_map.get(&k).unwrap_or(&"--".to_string()),
                v
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
            key_table: HashMap::new(),
            pod_class_table: HashMap::from_iter([(SELF, PodClass::Main)].into_iter()),
        }
    }
    pub fn add_signed_pod(&mut self, pod: &SignedPod) {
        self.input_signed_pods.push(pod.clone());
        pod.key_string_map.iter().for_each(|(hash, key)| {
            self.key_table.insert(hash.clone(), key.clone());
        });
        self.pod_class_table.insert(pod.id(), PodClass::Signed);
    }
    pub fn add_main_pod(&mut self, pod: MainPod) {
        self.pod_class_table.insert(pod.id(), PodClass::Main);
        pod.key_string_map.iter().for_each(|(hash, key)| {
            self.key_table.insert(hash.clone(), key.clone());
        });
        pod.pod_class_map.iter().for_each(|(pod_id, pod_class)| {
            self.pod_class_table
                .insert(pod_id.clone(), pod_class.clone());
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
        (&st).1.iter().for_each(|arg| match arg {
            StatementArg::Key(AnchoredKey(_, key)) => {
                self.key_table.insert(hash_str(key), key.clone());
            }
            _ => (),
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
        let key_string_map = inputs
            .public_statements
            .iter()
            .flat_map(|s| &s.1)
            .flat_map(|arg| match arg {
                StatementArg::Key(AnchoredKey(_, key)) => Some((hash_str(key), key.clone())),
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        let pod_class_map = (&inputs)
            .public_statements
            .into_iter()
            .flat_map(|s| &s.1)
            .flat_map(|arg| match arg {
                StatementArg::Key(AnchoredKey(Origin(pod_class, pod_id), _)) => {
                    Some((pod_id.clone(), pod_class.clone()))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();

        let (statements, operations, public_statements) = compiler.compile(inputs, params)?;
        let inputs = MainPodInputs {
            signed_pods: &self.input_signed_pods.iter().map(|p| &p.pod).collect_vec(),
            main_pods: &self.input_main_pods.iter().map(|p| &p.pod).collect_vec(),
            statements: &statements,
            operations: &operations,
            public_statements: &public_statements,
        };
        let pod = prover.prove(&self.params, inputs)?;
        Ok(MainPod {
            pod,
            key_string_map,
            pod_class_map,
        })
    }
}

#[derive(Debug)]
pub struct MainPod {
    pub pod: Box<dyn middleware::Pod>,
    // TODO: metadata
    pub key_string_map: HashMap<Hash, String>,
    pub pod_class_map: HashMap<PodId, PodClass>,
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

    pub fn compile<'a>(
        mut self,
        inputs: MainPodCompilerInputs<'a>,
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
        ($($arg:expr),+) => {vec![$(crate::frontend::OperationArg::from($arg)),*]}
    }

    #[macro_export]
    macro_rules! op {
        (eq, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::EqualFromEntries),
            crate::op_args!($($arg),*)) };
        (ne, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::NotEqualFromEntries),
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
        println!("{}", gov_id);

        let mut signer = MockSigner {
            pk: "ZooDeel".into(),
        };
        let pay_stub = pay_stub.sign(&mut signer)?;
        println!("{}", pay_stub);

        let mut signer = MockSigner {
            pk: "ZooOFAC".into(),
        };
        let sanction_list = sanction_list.sign(&mut signer)?;
        println!("{}", sanction_list);

        let kyc = zu_kyc_pod_builder(&params, &gov_id, &pay_stub, &sanction_list)?;
        println!("{}", kyc);

        let mut prover = MockProver {};
        let kyc = kyc.prove(&mut prover, &params)?;

        // TODO: prove kyc with MockProver and print it
        println!("{}", kyc);

        Ok(())
    }

    #[test]
    fn test_ethdos() -> Result<()> {
        let params = Params::default();

        let mut alice = MockSigner { pk: "Alice".into() };
        let mut bob = MockSigner { pk: "Bob".into() };
        let mut charlie = MockSigner {
            pk: "Charlie".into(),
        };

        // Alice attests that she is ETH friends with Charlie and Charlie
        // attests that he is ETH friends with Bob.
        let alice_attestation =
            eth_friend_signed_pod_builder(&params, charlie.pubkey().into()).sign(&mut alice)?;
        let charlie_attestation =
            eth_friend_signed_pod_builder(&params, bob.pubkey().into()).sign(&mut charlie)?;

        let mut prover = MockProver {};
        let alice_bob_ethdos = eth_dos_pod_builder(
            &params,
            &alice_attestation,
            &charlie_attestation,
            &bob.pubkey().into(),
        )?
        .prove(&mut prover, &params)?;

        Ok(())
    }

    #[test]
    fn test_front_great_boy() -> Result<()> {
        let great_boy = great_boy_pod_full_flow()?;
        println!("{}", great_boy);

        // TODO: prove kyc with MockProver and print it

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
