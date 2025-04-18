//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use std::{collections::HashMap, convert::From, fmt};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::middleware::{
    self, check_st_tmpl, hash_str, AnchoredKey, Key, MainPodInputs, NativeOperation,
    NativePredicate, OperationAux, OperationType, Params, PodId, PodProver, PodSigner, Predicate,
    Statement, StatementArg, Value, WildcardValue, EMPTY_VALUE, KEY_TYPE, SELF,
};

mod custom;
mod operation;
mod serialization;
pub use custom::*;
pub use operation::*;
use serialization::*;

/// This type is just for presentation purposes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum PodClass {
    #[default]
    Signed,
    Main,
}

#[derive(Clone, Debug)]
pub struct SignedPodBuilder {
    pub params: Params,
    pub kvs: HashMap<Key, Value>,
}

impl fmt::Display for SignedPodBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPodBuilder:")?;
        for (k, v) in self.kvs.iter().sorted_by_key(|kv| kv.0.hash()) {
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

    pub fn insert(&mut self, key: impl Into<Key>, value: impl Into<Value>) {
        self.kvs.insert(key.into(), value.into());
    }

    pub fn sign<S: PodSigner>(&self, signer: &mut S) -> Result<SignedPod> {
        // Sign POD with committed KV store.
        let pod = signer.sign(&self.params, &self.kvs)?;

        Ok(SignedPod::new(pod))
    }
}

/// SignedPod is a wrapper on top of backend::SignedPod, which additionally stores the
/// string<-->hash relation of the keys.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "SignedPodHelper", into = "SignedPodHelper")]
pub struct SignedPod {
    pub pod: Box<dyn middleware::Pod>,
    // We store a copy of the key values for quick access
    kvs: HashMap<Key, Value>,
}

impl fmt::Display for SignedPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedPod (id:{}):", self.id())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in self.pod.kvs().iter().sorted_by_key(|kv| kv.0.key.hash()) {
            writeln!(f, "  - {} = {}", k, v)?;
        }
        Ok(())
    }
}

impl SignedPod {
    pub fn new(pod: Box<dyn middleware::Pod>) -> Self {
        let kvs = pod
            .kvs()
            .into_iter()
            .map(|(AnchoredKey { key, .. }, v)| (key, v))
            .collect();
        Self { pod, kvs }
    }
    pub fn id(&self) -> PodId {
        self.pod.id()
    }
    pub fn verify(&self) -> Result<()> {
        self.pod.verify()
    }
    pub fn kvs(&self) -> &HashMap<Key, Value> {
        &self.kvs
    }
    pub fn get(&self, key: impl Into<Key>) -> Option<&Value> {
        self.kvs.get(&key.into())
    }
    // Returns the ValueOf statement that defines key if it exists.
    pub fn get_statement(&self, key: impl Into<Key>) -> Option<Statement> {
        let key: Key = key.into();
        self.kvs()
            .get(&key)
            .map(|value| Statement::ValueOf(AnchoredKey::from((self.id(), key)), value.clone()))
    }
}

/// The MainPodBuilder allows interactive creation of a MainPod by applying operations and creating
/// the corresponding statements.
#[derive(Debug)]
pub struct MainPodBuilder {
    pub params: Params,
    pub input_signed_pods: Vec<SignedPod>,
    pub input_main_pods: Vec<MainPod>,
    pub statements: Vec<Statement>,
    pub operations: Vec<Operation>,
    pub public_statements: Vec<Statement>,
    // Internal state
    /// Counter for constants created from literals
    const_cnt: usize,
    /// Map from (public, Value) to Key of already created literals via ValueOf statements.
    literals: HashMap<(bool, Value), Key>,
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
            literals: HashMap::new(),
        }
    }
    pub fn add_signed_pod(&mut self, pod: &SignedPod) {
        self.input_signed_pods.push(pod.clone());
    }
    pub fn add_main_pod(&mut self, pod: MainPod) {
        self.input_main_pods.push(pod);
    }
    pub fn insert(&mut self, public: bool, st_op: (Statement, Operation)) {
        // TODO: Do error handling instead of panic
        let (st, op) = st_op;
        if public {
            self.public_statements.push(st.clone());
        }
        if self.public_statements.len() > self.params.max_public_statements {
            panic!("too many public statements");
        }
        self.statements.push(st);
        self.operations.push(op);
        if self.statements.len() > self.params.max_statements {
            panic!("too many statements");
        }
    }

    /// Convert [OperationArg]s to [StatementArg]s for the operations that work with entries
    fn op_args_entries(
        &mut self,
        public: bool,
        args: &mut [OperationArg],
    ) -> Result<Vec<StatementArg>> {
        let mut st_args = Vec::new();
        // TODO: Rewrite without calling args() and instead using matches?
        for arg in args.iter_mut() {
            match arg {
                OperationArg::Statement(s) => {
                    if s.predicate() == Predicate::Native(NativePredicate::ValueOf) {
                        st_args.push(s.args()[0].clone())
                    } else {
                        panic!("Invalid statement argument.");
                    }
                }
                // todo: better error handling
                OperationArg::Literal(v) => {
                    let value_of_st = self.literal(public, v.clone())?;
                    *arg = OperationArg::Statement(value_of_st.clone());
                    st_args.push(value_of_st.args()[0].clone())
                }
                OperationArg::Entry(k, v) => {
                    st_args.push(StatementArg::Key(AnchoredKey::from((SELF, k.as_str()))));
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

    /// Lower syntactic sugar operation into backend compatible operation.
    /// - {Dict,Array,Set}Contains/NotContains becomes Contains/NotContains.
    fn lower_op(op: Operation) -> Operation {
        use NativeOperation::*;
        use OperationType::*;
        match op.0 {
            Native(DictContainsFromEntries) => {
                let [dict, key, value] = op.1.try_into().unwrap(); // TODO: Error handling
                Operation(Native(ContainsFromEntries), vec![dict, key, value], op.2)
            }
            Native(DictNotContainsFromEntries) => {
                let [dict, key] = op.1.try_into().unwrap(); // TODO: Error handling
                Operation(Native(NotContainsFromEntries), vec![dict, key], op.2)
            }
            Native(SetContainsFromEntries) => {
                let [set, value] = op.1.try_into().unwrap(); // TODO: Error handling
                let empty = OperationArg::Literal(Value::from(EMPTY_VALUE));
                Operation(Native(ContainsFromEntries), vec![set, value, empty], op.2)
            }
            Native(SetNotContainsFromEntries) => {
                let [set, value] = op.1.try_into().unwrap(); // TODO: Error handling
                Operation(Native(NotContainsFromEntries), vec![set, value], op.2)
            }
            Native(ArrayContainsFromEntries) => {
                let [array, index, value] = op.1.try_into().unwrap(); // TODO: Error handling
                Operation(Native(ContainsFromEntries), vec![array, index, value], op.2)
            }
            _ => op,
        }
    }

    /// Fills in auxiliary data if necessary/possible.
    fn fill_in_aux(op: Operation) -> Result<Operation> {
        use NativeOperation::{ContainsFromEntries, NotContainsFromEntries};
        use OperationAux as OpAux;
        use OperationType::Native;

        let op_type = &op.0;

        match (op_type, &op.2) {
            (Native(ContainsFromEntries), OpAux::None)
            | (Native(NotContainsFromEntries), OpAux::None) => {
                let container =
                    op.1.get(0)
                        .and_then(|arg| arg.value())
                        .ok_or(anyhow!("Invalid container argument for op {}.", op))?;
                let key =
                    op.1.get(1)
                        .and_then(|arg| arg.value())
                        .ok_or(anyhow!("Invalid key argument for op {}.", op))?;
                let proof = if op_type == &Native(ContainsFromEntries) {
                    container.prove_existence(key)?.1
                } else {
                    container.prove_nonexistence(key)?
                };
                Ok(Operation(op_type.clone(), op.1, OpAux::MerkleProof(proof)))
            }
            _ => Ok(op),
        }
    }

    fn op(&mut self, public: bool, op: Operation) -> Result<Statement, anyhow::Error> {
        use NativeOperation::*;
        let mut op = Self::fill_in_aux(Self::lower_op(op))?;
        let Operation(op_type, ref mut args, _) = &mut op;
        // TODO: argument type checking
        let pred = op_type.output_predicate().map(Ok).unwrap_or_else(|| {
            // We are dealing with a copy here.
            match (args).first() {
                Some(OperationArg::Statement(s)) if args.len() == 1 => Ok(s.predicate().clone()),
                _ => Err(anyhow!("Invalid arguments to copy operation: {:?}", args)),
            }
        })?;

        let st_args: Vec<StatementArg> = match op_type {
            OperationType::Native(o) => match o {
                None => vec![],
                NewEntry => self.op_args_entries(public, args)?,
                CopyStatement => match &args[0] {
                    OperationArg::Statement(s) => s.args().clone(),
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
                            OperationArg::Statement(Statement::Equal(ak0, ak1)),
                            OperationArg::Statement(Statement::Equal(ak2, ak3)),
                        ) => {
                            // st_args0 == vec![ak0, ak1]
                            // st_args1 == vec![ak1, ak2]
                            // output statement Equals(ak0, ak2)
                            if ak1 == ak2 {
                                vec![StatementArg::Key(ak0), StatementArg::Key(ak3)]
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
                    OperationArg::Statement(Statement::Gt(ak0, ak1)) => {
                        vec![StatementArg::Key(ak0), StatementArg::Key(ak1)]
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to gt-to-neq operation"));
                    }
                },
                LtToNotEqual => match args[0].clone() {
                    OperationArg::Statement(Statement::Lt(ak0, ak1)) => {
                        vec![StatementArg::Key(ak0), StatementArg::Key(ak1)]
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to lt-to-neq operation"));
                    }
                },
                SumOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement::ValueOf(ak0, v0)),
                        OperationArg::Statement(Statement::ValueOf(ak1, v1)),
                        OperationArg::Statement(Statement::ValueOf(ak2, v2)),
                    ) => {
                        let v0: i64 = v0.typed().try_into()?;
                        let v1: i64 = v1.typed().try_into()?;
                        let v2: i64 = v2.typed().try_into()?;
                        if v0 == v1 + v2 {
                            vec![
                                StatementArg::Key(ak0),
                                StatementArg::Key(ak1),
                                StatementArg::Key(ak2),
                            ]
                        } else {
                            return Err(anyhow!("Invalid arguments to sum-of operation"));
                        }
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to sum-of operation"));
                    }
                },
                ProductOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement::ValueOf(ak0, v0)),
                        OperationArg::Statement(Statement::ValueOf(ak1, v1)),
                        OperationArg::Statement(Statement::ValueOf(ak2, v2)),
                    ) => {
                        let v0: i64 = v0.typed().try_into()?;
                        let v1: i64 = v1.typed().try_into()?;
                        let v2: i64 = v2.typed().try_into()?;
                        if v0 == v1 * v2 {
                            vec![
                                StatementArg::Key(ak0),
                                StatementArg::Key(ak1),
                                StatementArg::Key(ak2),
                            ]
                        } else {
                            return Err(anyhow!("Invalid arguments to product-of operation"));
                        }
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to product-of operation"));
                    }
                },
                MaxOf => match (args[0].clone(), args[1].clone(), args[2].clone()) {
                    (
                        OperationArg::Statement(Statement::ValueOf(ak0, v0)),
                        OperationArg::Statement(Statement::ValueOf(ak1, v1)),
                        OperationArg::Statement(Statement::ValueOf(ak2, v2)),
                    ) => {
                        let v0: i64 = v0.typed().try_into()?;
                        let v1: i64 = v1.typed().try_into()?;
                        let v2: i64 = v2.typed().try_into()?;
                        if v0 == std::cmp::max(v1, v2) {
                            vec![
                                StatementArg::Key(ak0),
                                StatementArg::Key(ak1),
                                StatementArg::Key(ak2),
                            ]
                        } else {
                            return Err(anyhow!("Invalid arguments to max-of operation"));
                        }
                    }
                    _ => {
                        return Err(anyhow!("Invalid arguments to max-of operation"));
                    }
                },
                ContainsFromEntries => self.op_args_entries(public, args)?,
                NotContainsFromEntries => self.op_args_entries(public, args)?,
                // NOTE: Could we remove these and assume that this function is never called with
                // syntax sugar operations?
                DictContainsFromEntries => self.op_args_entries(public, args)?,
                DictNotContainsFromEntries => self.op_args_entries(public, args)?,
                SetContainsFromEntries => self.op_args_entries(public, args)?,
                SetNotContainsFromEntries => self.op_args_entries(public, args)?,
                ArrayContainsFromEntries => self.op_args_entries(public, args)?,
            },
            OperationType::Custom(cpr) => {
                let pred = &cpr.batch.predicates[cpr.index];
                if pred.statements.len() != args.len() {
                    return Err(anyhow!(
                        "Custom predicate operation needs {} statements but has {}.",
                        pred.statements.len(),
                        args.len()
                    ));
                }
                // All args should be statements to be pattern matched against statement templates.
                let args = args.iter().map(
                    |a| match a {
                        OperationArg::Statement(s) => Ok(s.clone()),
                        _ => Err(anyhow!("Invalid argument {} to operation corresponding to custom predicate {:?}.", a, cpr))
                    }
                ).collect::<Result<Vec<_>>>()?;

                let mut wildcard_map =
                    vec![Option::None; self.params.max_custom_predicate_wildcards];
                for (st_tmpl, st) in pred.statements.iter().zip(args.iter()) {
                    let st_args = st.args();
                    for (st_tmpl_arg, st_arg) in st_tmpl.args.iter().zip(&st_args) {
                        if !check_st_tmpl(st_tmpl_arg, st_arg, &mut wildcard_map) {
                            // TODO: Add wildcard_map in the error for better context
                            return Err(anyhow!("{} doesn't match {}", st, st_tmpl));
                        }
                    }
                }
                let v_default = WildcardValue::PodId(SELF);
                wildcard_map
                    .into_iter()
                    .take(pred.args_len)
                    .map(|v| StatementArg::WildcardLiteral(v.unwrap_or_else(|| v_default.clone())))
                    .collect()
            }
        };
        let st = Statement::from_args(pred, st_args).expect("valid arguments");
        self.insert(public, (st, op));

        Ok(self.statements[self.statements.len() - 1].clone())
    }

    /// Convenience method for introducing public constants.
    pub fn pub_literal(&mut self, v: impl Into<Value>) -> Result<Statement> {
        self.literal(true, v.into())
    }

    /// Convenience method for introducing private constants.
    pub fn priv_literal(&mut self, v: impl Into<Value>) -> Result<Statement> {
        self.literal(false, v.into())
    }

    fn literal(&mut self, public: bool, value: Value) -> Result<Statement> {
        let public_value = (public, value);
        if let Some(key) = self.literals.get(&public_value) {
            Ok(Statement::ValueOf(
                AnchoredKey::new(SELF, key.clone()),
                public_value.1,
            ))
        } else {
            let key = format!("c{}", self.const_cnt);
            self.literals
                .insert(public_value.clone(), Key::new(key.clone()));
            self.const_cnt += 1;
            self.op(
                public,
                Operation(
                    OperationType::Native(NativeOperation::NewEntry),
                    vec![OperationArg::Entry(key.clone(), public_value.1)],
                    OperationAux::None,
                ),
            )
        }
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
                Statement::ValueOf(AnchoredKey { pod_id: id, key }, value)
                    if id == pod_id && key.hash() == type_key_hash =>
                {
                    Some(Statement::ValueOf(
                        AnchoredKey::from((pod_id, KEY_TYPE)),
                        value,
                    ))
                }
                _ => None,
            })
            .ok_or(anyhow!("Missing POD type information in POD: {:?}", pod))?;
        // Replace instances of `SELF` with the POD ID for consistency
        // with `pub_statements` method.
        let public_statements = [type_statement]
            .into_iter()
            .chain(self.public_statements.clone().into_iter().map(|s| {
                let s_type = s.predicate();
                let s_args = s
                    .args()
                    .into_iter()
                    .map(|arg| match arg {
                        StatementArg::Key(AnchoredKey { pod_id: id, key }) if id == SELF => {
                            StatementArg::Key(AnchoredKey::new(pod_id, key))
                        }
                        _ => arg,
                    })
                    .collect();
                Statement::from_args(s_type, s_args).expect("valid arguments")
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
        writeln!(f, "  valid?  {}", self.pod.verify().is_ok())?;
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
}

struct MainPodCompilerInputs<'a> {
    // pub signed_pods: &'a [Box<dyn middleware::SignedPod>],
    // pub main_pods: &'a [Box<dyn middleware::MainPod>],
    pub statements: &'a [Statement],
    pub operations: &'a [Operation],
    pub public_statements: &'a [Statement],
}

/// The compiler converts frontend::Operation into middleware::Operation
struct MainPodCompiler {
    params: Params,
    // Output
    statements: Vec<Statement>,
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

    fn push_st_op(&mut self, st: Statement, op: middleware::Operation) {
        self.statements.push(st);
        self.operations.push(op);
        if self.statements.len() > self.params.max_statements {
            panic!("too many statements");
        }
    }

    fn compile_op_arg(&self, op_arg: &OperationArg) -> Option<Statement> {
        match op_arg {
            OperationArg::Statement(s) => Some(s.clone()),
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

    fn compile_op(&self, op: &Operation) -> Result<middleware::Operation> {
        // TODO: Take Merkle proof into account.
        let mop_args =
            op.1.iter()
                .flat_map(|arg| self.compile_op_arg(arg))
                .collect_vec();
        middleware::Operation::op(op.0.clone(), &mop_args, &op.2)
    }

    fn compile_st_op(&mut self, st: &Statement, op: &Operation, params: &Params) -> Result<()> {
        let middle_op = self.compile_op(op)?;
        let is_correct = middle_op.check(params, st)?;
        if !is_correct {
            // todo: improve error handling
            Err(anyhow!(
                "Compile failed due to invalid deduction:\n {} ⇏ {}",
                middle_op,
                st
            ))
        } else {
            self.push_st_op(st.clone(), middle_op);
            Ok(())
        }
    }

    pub fn compile(
        mut self,
        inputs: MainPodCompilerInputs<'_>,
        params: &Params,
    ) -> Result<(
        Vec<Statement>, // input statements
        Vec<middleware::Operation>,
        Vec<Statement>, // public statements
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
        }
        Ok((self.statements, self.operations, public_statements.to_vec()))
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
            $crate::op_args!(($key, $value)), $crate::middleware::OperationAux::None) };
        (eq, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::EqualFromEntries),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (ne, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::NotEqualFromEntries),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (gt, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::GtFromEntries),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (lt, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::LtFromEntries),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (transitive_eq, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::TransitiveEqualFromStatements),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (gt_to_ne, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::GtToNotEqual),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (lt_to_ne, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::LtToNotEqual),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (sum_of, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::SumOf),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (product_of, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::ProductOf),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (max_of, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::MaxOf),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (custom, $op:expr, $($arg:expr),+) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Custom($op),
            $crate::op_args!($($arg),*), $crate::middleware::OperationAux::None) };
        (dict_contains, $dict:expr, $key:expr, $value:expr) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::DictContainsFromEntries),
            $crate::op_args!($dict, $key, $value), $crate::middleware::OperationAux::None) };
        (dict_not_contains, $dict:expr, $key:expr) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::DictNotContainsFromEntries),
            $crate::op_args!($dict, $key), $crate::middleware::OperationAux::None) };
        (set_contains, $set:expr, $value:expr) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::SetContainsFromEntries),
            $crate::op_args!($set, $value), $crate::middleware::OperationAux::None) };
        (set_not_contains, $set:expr, $value:expr) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::SetNotContainsFromEntries),
            $crate::op_args!($set, $value), $crate::middleware::OperationAux::None) };
        (array_contains, $array:expr, $index:expr, $value:expr) => { $crate::frontend::Operation(
            $crate::middleware::OperationType::Native($crate::middleware::NativeOperation::ArrayContainsFromEntries),
            $crate::op_args!($array, $index, $value), $crate::middleware::OperationAux::None) };
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner},
        examples::{
            eth_dos_pod_builder, eth_friend_signed_pod_builder, great_boy_pod_full_flow,
            tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_sign_pod_builders,
        },
        middleware::{containers::Dictionary, Value},
    };

    // Check that frontend public statements agree with those
    // embedded in a MainPod.
    fn check_public_statements(pod: &MainPod) -> Result<()> {
        Ok(
            std::iter::zip(pod.public_statements.clone(), pod.pod.pub_statements()).try_for_each(
                |(fes, s)| {
                    crate::middleware::Statement::try_from(fes).map(|fes| assert_eq!(fes, s))
                },
            )?,
        )
    }

    // Check that frontend key-values agree with those embedded in a
    // SignedPod.
    fn check_kvs(pod: &SignedPod) -> Result<()> {
        let kvs = pod.kvs.clone().into_iter().collect::<HashMap<_, _>>();
        let embedded_kvs = pod
            .pod
            .kvs()
            .into_iter()
            .map(|(middleware::AnchoredKey { key, .. }, v)| (key, v))
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
            max_statement_args: 6,
            max_operation_args: 5,
            max_custom_predicate_arity: 5,
            max_custom_batch_size: 5,
            max_custom_predicate_wildcards: 12,
            ..Default::default()
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
            OperationAux::None,
        );
        let st1 = builder.op(true, op_eq1).unwrap();
        let op_eq2 = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::from((&signed_pod, "b")),
                OperationArg::from((&signed_pod, "a")),
            ],
            OperationAux::None,
        );
        let st2 = builder.op(true, op_eq2).unwrap();

        let op_eq3 = Operation(
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
            vec![OperationArg::Statement(st1), OperationArg::Statement(st2)],
            OperationAux::None,
        );
        builder.op(true, op_eq3).unwrap();

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
    fn test_dictionaries() -> Result<()> {
        let params = Params::default();
        let mut builder = SignedPodBuilder::new(&params);

        let mut my_dict_kvs: HashMap<Key, Value> = HashMap::new();
        my_dict_kvs.insert(Key::from("a"), Value::from(1));
        my_dict_kvs.insert(Key::from("b"), Value::from(2));
        my_dict_kvs.insert(Key::from("c"), Value::from(3));
        //        let my_dict_as_mt = MerkleTree::new(5, &my_dict_kvs).unwrap();
        //        let dict = Dictionary { mt: my_dict_as_mt };
        let dict = Dictionary::new(my_dict_kvs)?;
        let dict_root = Value::from(dict.clone());
        builder.insert("dict", dict_root);

        let mut signer = MockSigner {
            pk: "signer".into(),
        };
        let pod = builder.sign(&mut signer).unwrap();

        let mut builder = MainPodBuilder::new(&params);
        builder.add_signed_pod(&pod);
        let st0 = pod.get_statement("dict").unwrap();
        let st1 = builder.op(true, op!(new_entry, ("key", "a"))).unwrap();
        let st2 = builder.literal(false, Value::from(1)).unwrap();

        builder
            .pub_op(Operation(
                // OperationType
                OperationType::Native(NativeOperation::DictContainsFromEntries),
                // Vec<OperationArg>
                vec![
                    OperationArg::Statement(st0),
                    OperationArg::Statement(st1),
                    OperationArg::Statement(st2),
                ],
                OperationAux::MerkleProof(dict.prove(&Key::from("a")).unwrap().1),
            ))
            .unwrap();
        let mut main_prover = MockProver {};
        let main_pod = builder.prove(&mut main_prover, &params).unwrap();

        println!("{}", main_pod);

        Ok(())
    }

    #[should_panic]
    #[test]
    fn test_incorrect_pod() {
        // try to insert the same key multiple times
        // right now this is not caught when you build the pod,
        // but it is caught on verify
        env_logger::init();

        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params);
        let st = Statement::ValueOf(AnchoredKey::from((SELF, "a")), Value::from(3));
        let op_new_entry = Operation(
            OperationType::Native(NativeOperation::NewEntry),
            vec![],
            OperationAux::None,
        );
        builder.insert(false, (st, op_new_entry.clone()));

        let st = Statement::ValueOf(AnchoredKey::from((SELF, "a")), Value::from(28));
        builder.insert(false, (st, op_new_entry.clone()));

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();
        pod.pod.verify().unwrap();

        // try to insert a statement that doesn't follow from the operation
        // right now the mock prover catches this when it calls compile()
        let params = Params::default();
        let mut builder = MainPodBuilder::new(&params);
        let self_a = AnchoredKey::from((SELF, "a"));
        let self_b = AnchoredKey::from((SELF, "b"));
        let value_of_a = Statement::ValueOf(self_a.clone(), Value::from(3));
        let value_of_b = Statement::ValueOf(self_b.clone(), Value::from(27));

        builder.insert(false, (value_of_a.clone(), op_new_entry.clone()));
        builder.insert(false, (value_of_b.clone(), op_new_entry));
        let st = Statement::Equal(self_a, self_b);
        let op = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::Statement(value_of_a),
                OperationArg::Statement(value_of_b),
            ],
            OperationAux::None,
        );
        builder.insert(false, (st, op));

        let mut prover = MockProver {};
        let pod = builder.prove(&mut prover, &params).unwrap();
        pod.pod.verify().unwrap();
    }
}
