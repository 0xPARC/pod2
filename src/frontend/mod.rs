//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use crate::frontend::serialization::*;
use crate::middleware::{
    self, hash_str, Hash, MainPodInputs, NativeOperation, NativePredicate, Params, PodId,
    PodProver, PodSigner, SELF,
};
use crate::middleware::{OperationType, Predicate, KEY_SIGNER, KEY_TYPE};
use anyhow::{anyhow, Error, Result};
use containers::{Array, Dictionary, Set};
use env_logger;
use itertools::Itertools;
use log::error;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::convert::From;
use std::{fmt, hash as h};

pub mod containers;
mod custom;
mod operation;
mod serialization;
mod statement;
pub use custom::*;
pub use operation::*;
pub use statement::*;

/// This type is just for presentation purposes.
#[derive(Clone, Debug, Default, h::Hash, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub enum PodClass {
    #[default]
    Signed,
    Main,
}

// An Origin, which represents a reference to an ancestor POD.
#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Default, Serialize, Deserialize, JsonSchema)]
pub struct Origin {
    pub pod_class: PodClass,
    pub pod_id: PodId,
}

impl Origin {
    pub fn new(pod_class: PodClass, pod_id: PodId) -> Self {
        Self { pod_class, pod_id }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[schemars(transform = serialization::transform_value_schema)]
pub enum Value {
    // Serde cares about the order of the enum variants, with untagged variants
    // appearing at the end.
    // Variants without "untagged" will be serialized as "tagged" values by
    // default, meaning that a Set appears in JSON as {"Set":[...]}
    // and not as [...]
    // Arrays, Strings and Booleans are untagged, as there is a natural JSON
    // representation for them that is unambiguous to deserialize and is fully
    // compatible with the semantics of the POD types.
    // As JSON integers do not specify precision, and JavaScript is limited to
    // 53-bit precision for integers, integers are represented as tagged
    // strings, with a custom serializer and deserializer.
    // TAGGED TYPES:
    Set(Set),
    Dictionary(Dictionary),
    Int(
        #[serde(serialize_with = "serialize_i64", deserialize_with = "deserialize_i64")]
        #[schemars(with = "String", regex(pattern = r"^\d+$"))]
        i64,
    ),
    // Uses the serialization for middleware::Value:
    Raw(middleware::Value),
    // UNTAGGED TYPES:
    #[serde(untagged)]
    #[schemars(skip)]
    Array(Array),
    #[serde(untagged)]
    #[schemars(skip)]
    String(String),
    #[serde(untagged)]
    #[schemars(skip)]
    Bool(bool),
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
            Value::Dictionary(d) => d.middleware_dict().commitment().value(),
            Value::Set(s) => s.middleware_set().commitment().value(),
            Value::Array(a) => a.middleware_array().commitment().value(),
            Value::Raw(v) => *v,
        }
    }
}

impl From<middleware::Value> for Value {
    fn from(v: middleware::Value) -> Self {
        Self::Raw(v)
    }
}

impl TryInto<i64> for Value {
    type Error = Error;
    fn try_into(self) -> std::result::Result<i64, Self::Error> {
        if let Value::Int(n) = self {
            Ok(n)
        } else {
            Err(anyhow!("Value not an int"))
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Int(v) => write!(f, "{}", v),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Dictionary(d) => write!(f, "dict:{}", d.middleware_dict().commitment()),
            Value::Set(s) => write!(f, "set:{}", s.middleware_set().commitment()),
            Value::Array(a) => write!(f, "arr:{}", a.middleware_array().commitment()),
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
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "SignedPodHelper", into = "SignedPodHelper")]
pub struct SignedPod {
    pub pod: Box<dyn middleware::Pod>,
    /// Key-value pairs as represented in the frontend. These should
    /// correspond to the entries of `pod.kvs()` after hashing and
    /// replacing each key with its corresponding anchored key.
    #[serde(serialize_with = "ordered_map")]
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
        Origin::new(PodClass::Signed, self.id())
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

#[derive(Clone, Debug, PartialEq, Eq, h::Hash, Serialize, Deserialize, JsonSchema)]
pub struct AnchoredKey {
    pub origin: Origin,
    pub key: String,
}

impl AnchoredKey {
    pub fn new(origin: Origin, key: String) -> Self {
        Self { origin, key }
    }
}

impl From<AnchoredKey> for middleware::AnchoredKey {
    fn from(ak: AnchoredKey) -> Self {
        middleware::AnchoredKey(ak.origin.pod_id, hash_str(&ak.key))
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
            .flat_map(|s| &s.args)
            .flat_map(|arg| match arg {
                StatementArg::Key(AnchoredKey {
                    origin: Origin { pod_class, pod_id },
                    key,
                }) => Some((*pod_id, pod_class.clone(), hash_str(key), key.clone())),
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
                    if s.predicate == Predicate::Native(NativePredicate::ValueOf) {
                        st_args.push(s.args[0].clone())
                    } else {
                        panic!("Invalid statement argument.");
                    }
                }
                // todo: better error handling
                OperationArg::Literal(v) => {
                    let value_of_st = self.literal(public, v)?;
                    *arg = OperationArg::Statement(value_of_st.clone());
                    st_args.push(value_of_st.args[0].clone())
                }
                OperationArg::Entry(k, v) => {
                    st_args.push(StatementArg::Key(AnchoredKey::new(
                        Origin::new(PodClass::Main, SELF),
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
        let pred = op_type
            .output_predicate()
            .map(|p| Ok(p))
            .unwrap_or_else(|| {
                // We are dealing with a copy here.
                match (&args).get(0) {
                    Some(OperationArg::Statement(s)) if args.len() == 1 => Ok(s.predicate.clone()),
                    _ => Err(anyhow!("Invalid arguments to copy operation: {:?}", args)),
                }
            })?;

        let st_args: Vec<StatementArg> = match op_type {
            OperationType::Native(o) => match o {
                None => vec![],
                NewEntry => self.op_args_entries(public, args)?,
                CopyStatement => match &args[0] {
                    OperationArg::Statement(s) => s.args.clone(),
                    _ => {
                        return Err(anyhow!("Invalid arguments to copy operation: {}", op));
                    }
                },
                EqualFromEntries => self.op_args_entries(public, args)?,
                NotEqualFromEntries => self.op_args_entries(public, args)?,
                GtFromEntries => self.op_args_entries(public, args)?,
                LtFromEntries => self.op_args_entries(public, args)?,
                TransitiveEqualFromStatements => {
                    match (args[0].clone(), args[1].clone()) {
                        (
                            OperationArg::Statement(Statement {
                                predicate: Predicate::Native(NativePredicate::Equal),
                                args: st0_args,
                            }),
                            OperationArg::Statement(Statement {
                                predicate: Predicate::Native(NativePredicate::Equal),
                                args: st1_args,
                            }),
                        ) => {
                            // st_args0 == vec![ak0, ak1]
                            // st_args1 == vec![ak1, ak2]
                            // output statement Equals(ak0, ak2)
                            if st0_args[1] == st1_args[0] {
                                vec![st0_args[0].clone(), st1_args[1].clone()]
                            } else {
                                return Err(anyhow!(
                                    "Invalid arguments to transitive equality operation"
                                ));
                            }
                        }
                        _ => {
                            return Err(anyhow!(
                                "Invalid arguments to transitive equality operation"
                            ));
                        }
                    }
                }
                GtToNotEqual => match args[0].clone() {
                    OperationArg::Statement(Statement {
                        predicate: Predicate::Native(NativePredicate::Gt),
                        args: st_args,
                    }) => {
                        vec![st_args[0].clone()]
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to gt-to-neq operation"));
                    }
                },
                LtToNotEqual => match args[0].clone() {
                    OperationArg::Statement(Statement {
                        predicate: Predicate::Native(NativePredicate::Lt),
                        args: st_args,
                    }) => {
                        vec![st_args[0].clone()]
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to lt-to-neq operation"));
                    }
                },
                ContainsFromEntries => self.op_args_entries(public, args)?,
                NotContainsFromEntries => self.op_args_entries(public, args)?,
                SumOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st0_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st1_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st2_args,
                        }),
                    ) => {
                        let st_args: Vec<StatementArg> = match (
                            st0_args[1].clone(),
                            st1_args[1].clone(),
                            st2_args[1].clone(),
                        ) {
                            (
                                StatementArg::Literal(v0),
                                StatementArg::Literal(v1),
                                StatementArg::Literal(v2),
                            ) => {
                                let v0: i64 = v0.clone().try_into()?;
                                let v1: i64 = v1.clone().try_into()?;
                                let v2: i64 = v2.clone().try_into()?;
                                if v0 == v1 + v2 {
                                    vec![
                                        st0_args[0].clone(),
                                        st1_args[0].clone(),
                                        st2_args[0].clone(),
                                    ]
                                } else {
                                    return Err(anyhow!("Invalid arguments to sum-of operation"));
                                }
                            }
                            _ => {
                                return Err(anyhow!("Invalid arguments to sum-of operation"));
                            }
                        };
                        st_args
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to sum-of operation"));
                    }
                },
                ProductOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st0_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st1_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st2_args,
                        }),
                    ) => {
                        let st_args: Vec<StatementArg> = match (
                            st0_args[1].clone(),
                            st1_args[1].clone(),
                            st2_args[1].clone(),
                        ) {
                            (
                                StatementArg::Literal(v0),
                                StatementArg::Literal(v1),
                                StatementArg::Literal(v2),
                            ) => {
                                let v0: i64 = v0.clone().try_into()?;
                                let v1: i64 = v1.clone().try_into()?;
                                let v2: i64 = v2.clone().try_into()?;
                                if v0 == v1 * v2 {
                                    vec![
                                        st0_args[0].clone(),
                                        st1_args[0].clone(),
                                        st2_args[0].clone(),
                                    ]
                                } else {
                                    return Err(anyhow!(
                                        "Invalid arguments to product-of operation"
                                    ));
                                }
                            }
                            _ => {
                                return Err(anyhow!("Invalid arguments to product-of operation"));
                            }
                        };
                        st_args
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to product-of operation"));
                    }
                },
                MaxOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st0_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st1_args,
                        }),
                        OperationArg::Statement(Statement {
                            predicate: Predicate::Native(NativePredicate::ValueOf),
                            args: st2_args,
                        }),
                    ) => {
                        let st_args: Vec<StatementArg> = match (
                            st0_args[1].clone(),
                            st1_args[1].clone(),
                            st2_args[1].clone(),
                        ) {
                            (
                                StatementArg::Literal(v0),
                                StatementArg::Literal(v1),
                                StatementArg::Literal(v2),
                            ) => {
                                let v0: i64 = v0.clone().try_into()?;
                                let v1: i64 = v1.clone().try_into()?;
                                let v2: i64 = v2.clone().try_into()?;
                                if v0 == std::cmp::max(v1, v2) {
                                    vec![
                                        st0_args[0].clone(),
                                        st1_args[0].clone(),
                                        st2_args[0].clone(),
                                    ]
                                } else {
                                    return Err(anyhow!("Invalid arguments to max-of operation"));
                                }
                            }
                            _ => {
                                return Err(anyhow!("Invalid arguments to max-of operation"));
                            }
                        };
                        st_args
                    }
                    RenameContainedBy => todo!(),
                    _ => {
                        return Err(anyhow!("Invalid arguments to operation"));
                    }
                },
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

                output_arg_values
                    .chunks(2)
                    .map(|chunk| {
                        Ok(StatementArg::Key(AnchoredKey::new(
                            Origin::new(
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
                    .collect::<Result<Vec<_>>>()?
            }
        };
        let st = Statement::new(pred, st_args);
        self.operations.push(op);
        if public {
            self.public_statements.push(st.clone());
        }

        // Add key-hash pairs in statement to table.
        st.args.iter().for_each(|arg| {
            if let StatementArg::Key(AnchoredKey { origin: _, key }) = arg {
                self.key_table.insert(hash_str(key), key.clone());
            }
        });

        self.statements.push(st);
        Ok(self.statements[self.statements.len() - 1].clone())
    }

    /// Convenience method for introducing public constants.
    pub fn pub_literal<V: Clone + Into<Value>>(&mut self, v: &V) -> Result<Statement> {
        self.literal(true, v)
    }

    /// Convenience method for introducing private constants.
    pub fn priv_literal<V: Clone + Into<Value>>(&mut self, v: &V) -> Result<Statement> {
        self.literal(false, v)
    }

    fn literal<V: Clone + Into<Value>>(&mut self, public: bool, v: &V) -> Result<Statement> {
        let v: Value = v.clone().into();
        let k = format!("c{}", self.const_cnt);
        self.const_cnt += 1;
        self.op(
            public,
            Operation(
                OperationType::Native(NativeOperation::NewEntry),
                vec![OperationArg::Entry(k.clone(), v)],
            ),
        )
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
                ) if id == pod_id && key == type_key_hash => Some(Statement {
                    predicate: Predicate::Native(NativePredicate::ValueOf),
                    args: vec![
                        StatementArg::Key(AnchoredKey::new(
                            Origin::new(PodClass::Main, pod_id),
                            KEY_TYPE.to_string(),
                        )),
                        StatementArg::Literal(value.into()),
                    ],
                }),
                _ => None,
            })
            .ok_or(anyhow!("Missing POD type information in POD: {:?}", pod))?;
        // Replace instances of `SELF` with the POD ID for consistency
        // with `pub_statements` method.
        let public_statements = [type_statement]
            .into_iter()
            .chain(self.public_statements.clone().into_iter().map(|s| {
                let s_type = s.predicate;
                let s_args = s
                    .args
                    .into_iter()
                    .map(|arg| match arg {
                        StatementArg::Key(AnchoredKey {
                            origin:
                                Origin {
                                    pod_class: class,
                                    pod_id: id,
                                },
                            key,
                        }) if id == SELF => {
                            StatementArg::Key(AnchoredKey::new(Origin::new(class, pod_id), key))
                        }
                        _ => arg,
                    })
                    .collect();
                Statement::new(s_type, s_args)
            }))
            .collect();

        Ok(MainPod {
            pod,
            public_statements,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "MainPodHelper", into = "MainPodHelper")]
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
        Origin::new(PodClass::Main, self.id())
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
        (new_entry, ($key:expr, $value:expr)) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::NewEntry),
            $crate::op_args!(($key, $value))) };
        (eq, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::EqualFromEntries),
            $crate::op_args!($($arg),*)) };
        (ne, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::NotEqualFromEntries),
            $crate::op_args!($($arg),*)) };
        (gt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::GtFromEntries),
            crate::op_args!($($arg),*)) };
        (lt, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::LtFromEntries),
            crate::op_args!($($arg),*)) };
        (transitive_eq, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::TransitiveEqualFromStatements),
            crate::op_args!($($arg),*)) };
        (gt_to_ne, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::GtToNotEqual),
            crate::op_args!($($arg),*)) };
        (lt_to_ne, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::LtToNotEqual),
            crate::op_args!($($arg),*)) };
        (contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::ContainsFromEntries),
            crate::op_args!($($arg),*)) };
        (not_contains, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::NotContainsFromEntries),
            crate::op_args!($($arg),*)) };
        (sum_of, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::SumOf),
            crate::op_args!($($arg),*)) };
        (product_of, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::ProductOf),
            crate::op_args!($($arg),*)) };
        (max_of, $($arg:expr),+) => { crate::frontend::Operation(
            crate::middleware::OperationType::Native(crate::middleware::NativeOperation::MaxOf),
            crate::op_args!($($arg),*)) };
        (custom, $op:expr, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Custom($op),
            $crate::op_args!($($arg),*)) };
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
        let params = Params {
            max_input_signed_pods: 3,
            max_input_main_pods: 3,
            max_statements: 31,
            max_signed_pod_values: 8,
            max_public_statements: 10,
            max_statement_args: 5,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
        };

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
    // Transitive equality not implemented yet
    #[should_panic]
    fn test_equal() {
        let params = Params::default();
        let mut signed_builder = SignedPodBuilder::new(&params);
        signed_builder.insert("a", 1);
        signed_builder.insert("b", 1);
        let mut signer = MockSigner { pk: "key".into() };
        let signed_pod = signed_builder.sign(&mut signer).unwrap();

        let mut builder = MainPodBuilder::new(&params);
        builder.add_signed_pod(&signed_pod);

        //let op_val1 = Operation{
        //    OperationType::Native(NativeOperation::CopyStatement),
        //    signed_pod.
        //}

        let op_eq1 = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::from((&signed_pod, "a")),
                OperationArg::from((&signed_pod, "b")),
            ],
        );
        let st1 = builder.op(true, op_eq1).unwrap();
        let op_eq2 = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::from((&signed_pod, "b")),
                OperationArg::from((&signed_pod, "a")),
            ],
        );
        let st2 = builder.op(true, op_eq2).unwrap();

        let op_eq3 = Operation(
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
            vec![OperationArg::Statement(st1), OperationArg::Statement(st2)],
        );
        let st3 = builder.op(true, op_eq3);

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();

        println!("{}", pod);
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

    #[test]
    #[should_panic]
    fn test_incorrect_pod() {
        // try to insert the same key multiple times
        // right now this is not caught when you build the pod,
        // but it is caught on verify
        env_logger::init();

        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params);
        builder.insert((
            Statement::new(
                Predicate::Native(NativePredicate::ValueOf),
                vec![
                    StatementArg::Key(AnchoredKey::new(
                        Origin::new(PodClass::Main, SELF),
                        "a".into(),
                    )),
                    StatementArg::Literal(Value::Int(3)),
                ],
            ),
            Operation(OperationType::Native(NativeOperation::NewEntry), vec![]),
        ));
        builder.insert((
            Statement::new(
                Predicate::Native(NativePredicate::ValueOf),
                vec![
                    StatementArg::Key(AnchoredKey::new(
                        Origin::new(PodClass::Main, SELF),
                        "a".into(),
                    )),
                    StatementArg::Literal(Value::Int(28)),
                ],
            ),
            Operation(OperationType::Native(NativeOperation::NewEntry), vec![]),
        ));

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();
        pod.pod.verify();

        // try to insert a statement that doesn't follow from the operation
        // right now the mock prover catches this when it calls compile()
        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params);
        let self_a = AnchoredKey::new(Origin::new(PodClass::Main, SELF), "a".into());
        let self_b = AnchoredKey::new(Origin::new(PodClass::Main, SELF), "b".into());
        let value_of_a = Statement::new(
            Predicate::Native(NativePredicate::ValueOf),
            vec![
                StatementArg::Key(AnchoredKey::new(
                    Origin::new(PodClass::Main, SELF),
                    "a".into(),
                )),
                StatementArg::Literal(Value::Int(3)),
            ],
        );
        let value_of_b = Statement::new(
            Predicate::Native(NativePredicate::ValueOf),
            vec![
                StatementArg::Key(AnchoredKey::new(
                    Origin::new(PodClass::Main, SELF),
                    "b".into(),
                )),
                StatementArg::Literal(Value::Int(27)),
            ],
        );

        builder.insert((
            value_of_a.clone(),
            Operation(OperationType::Native(NativeOperation::NewEntry), vec![]),
        ));
        builder.insert((
            value_of_b.clone(),
            Operation(OperationType::Native(NativeOperation::NewEntry), vec![]),
        ));
        builder.insert((
            Statement::new(
                Predicate::Native(NativePredicate::Equal),
                vec![StatementArg::Key(self_a), StatementArg::Key(self_b)],
            ),
            Operation(
                OperationType::Native(NativeOperation::EqualFromEntries),
                vec![
                    OperationArg::Statement(value_of_a),
                    OperationArg::Statement(value_of_b),
                ],
            ),
        ));

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();
        pod.pod.verify();
    }
}
