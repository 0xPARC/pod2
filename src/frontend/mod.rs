//! The frontend includes the user-level abstractions and user-friendly types to define and work
//! with Pods.

use std::{
    collections::{HashMap, HashSet},
    convert::From,
    fmt,
};

use itertools::Itertools;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
pub use serialization::SerializedMainPod;

use crate::middleware::{
    self, check_custom_pred, check_st_tmpl, containers::Dictionary, hash_op, max_op, prod_op,
    sum_op, AnchoredKey, Hash, Key, MainPodInputs, MainPodProver, NativeOperation, OperationAux,
    OperationType, Params, PublicKey, RawValue, Signature, Signer, Statement, StatementArg, VDSet,
    Value, ValueRef,
};

mod custom;
mod error;
mod operation;
mod pod_request;
mod serialization;
pub use custom::*;
pub use error::*;
pub use operation::*;
pub use pod_request::*;

#[derive(Clone, Debug)]
pub struct SignedDictBuilder {
    pub params: Params,
    pub kvs: HashMap<Key, Value>,
}

impl fmt::Display for SignedDictBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedDictBuilder:")?;
        for (k, v) in self.kvs.iter().sorted_by_key(|kv| kv.0.hash()) {
            writeln!(f, "  - {}: {}", k, v)?;
        }
        Ok(())
    }
}

impl SignedDictBuilder {
    pub fn new(params: &Params) -> Self {
        Self {
            params: params.clone(),
            kvs: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key: impl Into<Key>, value: impl Into<Value>) {
        self.kvs.insert(key.into(), value.into());
    }

    pub fn sign<S: Signer>(&self, signer: &S) -> Result<SignedDict> {
        // Sign committed KV store.
        let dict = Dictionary::new(self.kvs.clone());
        // NOTE: This is the same way that `TypedValue::Dictionary` computes the `RawValue`
        let msg_raw = RawValue::from(dict.commitment());
        let signature = signer.sign(msg_raw);

        Ok(SignedDict {
            dict,
            public_key: signer.public_key(),
            signature,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
// #[serde(try_from = "SerializedSignedDict", into = "SerializedSignedDict")]
pub struct SignedDict {
    pub dict: Dictionary,
    pub public_key: PublicKey,
    pub signature: Signature,
}

impl fmt::Display for SignedDict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SignedDict (raw:{}):", self.dict.commitment())?;
        // Note: current version iterates sorting by keys of the kvs, but the merkletree defined at
        // https://0xparc.github.io/pod2/merkletree.html will not need it since it will be
        // deterministic based on the keys values not on the order of the keys when added into the
        // tree.
        for (k, v) in self.dict.kvs().iter().sorted_by_key(|kv| kv.0.hash()) {
            writeln!(f, "  - {} = {}", k, v)?;
        }
        Ok(())
    }
}

impl SignedDict {
    pub fn verify(&self) -> Result<()> {
        self.signature
            .verify(self.public_key, RawValue::from(self.dict.commitment()))
            .then_some(())
            .ok_or(Error::custom("Invalid signature!"))
    }
    pub fn kvs(&self) -> &HashMap<Key, Value> {
        self.dict.kvs()
    }
    pub fn get(&self, key: impl Into<Key>) -> Option<&Value> {
        self.kvs().get(&key.into())
    }
    // Returns the Contains statement that defines key if it exists.
    pub fn get_statement(&self, key: impl Into<Key>) -> Option<Statement> {
        let key: Key = key.into();
        self.kvs().get(&key).map(|value| {
            Statement::Contains(
                ValueRef::Literal(Value::from(self.dict.clone())),
                ValueRef::Literal(Value::from(key.name())),
                ValueRef::Literal(value.clone()),
            )
        })
    }
}

/// The MainPodBuilder allows interactive creation of a MainPod by applying operations and creating
/// the corresponding statements.
#[derive(Debug)]
pub struct MainPodBuilder {
    pub params: Params,
    pub vd_set: VDSet,
    pub input_pods: Vec<MainPod>,
    pub statements: Vec<Statement>,
    pub operations: Vec<Operation>,
    pub public_statements: Vec<Statement>,
    // Internal state
    dict_contains: Vec<(Value, Value)>, // (root, key)
}

impl fmt::Display for MainPodBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MainPod:")?;
        writeln!(f, "  input_main_pods:")?;
        for in_pod in &self.input_pods {
            writeln!(f, "    - {}", in_pod.statements_hash())?;
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
    pub fn new(params: &Params, vd_set: &VDSet) -> Self {
        Self {
            params: params.clone(),
            vd_set: vd_set.clone(),
            input_pods: Vec::new(),
            statements: Vec::new(),
            operations: Vec::new(),
            public_statements: Vec::new(),
            dict_contains: Vec::new(),
        }
    }
    pub fn add_pod(&mut self, pod: MainPod) -> Result<()> {
        self.input_pods.push(pod);
        match self.input_pods.len() > self.params.max_input_pods {
            true => Err(Error::too_many_input_pods(
                self.input_pods.len(),
                self.params.max_input_pods,
            )),
            _ => Ok(()),
        }
    }
    pub fn insert(&mut self, public: bool, st_op: (Statement, Operation)) -> Result<()> {
        // TODO: Do error handling instead of panic
        let (st, op) = st_op;

        // If we're adding a Contains statement with literal arguments (an Entry), track it in
        // `dict_contains` to avoid adding it again via `Self::add_entries_contains`.
        if let Statement::Contains(
            ValueRef::Literal(dict),
            ValueRef::Literal(key),
            ValueRef::Literal(_),
        ) = &st
        {
            let root_key = (dict.clone(), key.clone());
            self.dict_contains.push(root_key);
        }

        if public {
            self.public_statements.push(st.clone());
        }
        if self.public_statements.len() > self.params.max_public_statements {
            return Err(Error::too_many_public_statements(
                self.public_statements.len(),
                self.params.max_public_statements,
            ));
        }
        self.statements.push(st);
        self.operations.push(op);
        if self.statements.len() > self.params.max_statements {
            return Err(Error::too_many_statements(
                self.statements.len(),
                self.params.max_statements,
            ));
        }
        Ok(())
    }

    pub fn pub_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(true, vec![], op)
    }

    pub fn priv_op(&mut self, op: Operation) -> Result<Statement> {
        self.op(false, vec![], op)
    }

    /// Lower syntactic sugar operation into backend compatible operation.
    /// - {Dict,Array,Set}Contains/NotContains becomes Contains/NotContains.
    /// - GtEqFromEntries/GtFromEntries/GtToNotEqual becomes
    ///   LtEqFromEntries/LtFromEntries/LtToNotEqual.
    fn lower_op(op: Operation) -> Result<Operation> {
        use NativeOperation::*;
        use OperationType::*;
        let op_type = op.0.clone();
        match op.0 {
            Native(DictContainsFromEntries) => <[_; 3]>::try_from(op.1).map(|[dict, key, value]| {
                Operation(Native(ContainsFromEntries), vec![dict, key, value], op.2)
            }),
            Native(DictNotContainsFromEntries) => <[_; 2]>::try_from(op.1).map(|[dict, key]| {
                Operation(Native(NotContainsFromEntries), vec![dict, key], op.2)
            }),
            Native(SetContainsFromEntries) => <[_; 2]>::try_from(op.1).map(|[set, value]| {
                Operation(
                    Native(ContainsFromEntries),
                    vec![set, value.clone(), value],
                    op.2,
                )
            }),
            Native(SetNotContainsFromEntries) => <[_; 2]>::try_from(op.1).map(|[set, value]| {
                Operation(Native(NotContainsFromEntries), vec![set, value], op.2)
            }),
            Native(ArrayContainsFromEntries) => {
                <[_; 3]>::try_from(op.1).map(|[array, index, value]| {
                    Operation(Native(ContainsFromEntries), vec![array, index, value], op.2)
                })
            }
            Native(GtEqFromEntries) => <[_; 2]>::try_from(op.1).map(|[entry1, entry2]| {
                Operation(Native(LtEqFromEntries), vec![entry2, entry1], op.2)
            }),
            Native(GtFromEntries) => <[_; 2]>::try_from(op.1).map(|[entry1, entry2]| {
                Operation(Native(LtFromEntries), vec![entry2, entry1], op.2)
            }),
            Native(GtToNotEqual) => Ok(Operation(Native(LtToNotEqual), op.1, op.2)),
            Native(DictInsertFromEntries) => {
                <[_; 4]>::try_from(op.1).map(|[new_dict, old_dict, key, value]| {
                    Operation(
                        Native(ContainerInsertFromEntries),
                        vec![new_dict, old_dict, key, value],
                        op.2,
                    )
                })
            }
            Native(DictUpdateFromEntries) => {
                <[_; 4]>::try_from(op.1).map(|[new_dict, old_dict, key, value]| {
                    Operation(
                        Native(ContainerUpdateFromEntries),
                        vec![new_dict, old_dict, key, value],
                        op.2,
                    )
                })
            }
            Native(DictDeleteFromEntries) => {
                <[_; 3]>::try_from(op.1).map(|[new_dict, old_dict, key]| {
                    Operation(
                        Native(ContainerDeleteFromEntries),
                        vec![new_dict, old_dict, key],
                        op.2,
                    )
                })
            }
            Native(SetInsertFromEntries) => {
                <[_; 3]>::try_from(op.1).map(|[new_set, old_set, value]| {
                    Operation(
                        Native(ContainerInsertFromEntries),
                        vec![new_set, old_set, value.clone(), value],
                        op.2,
                    )
                })
            }
            Native(SetDeleteFromEntries) => {
                <[_; 3]>::try_from(op.1).map(|[new_set, old_set, value]| {
                    Operation(
                        Native(ContainerDeleteFromEntries),
                        vec![new_set, old_set, value],
                        op.2,
                    )
                })
            }
            Native(ArrayUpdateFromEntries) => {
                <[_; 4]>::try_from(op.1).map(|[new_arr, old_arr, i, value]| {
                    Operation(
                        Native(ContainerUpdateFromEntries),
                        vec![new_arr, old_arr, i, value],
                        op.2,
                    )
                })
            }
            _ => Ok(op),
        }
        .map_err(|_| {
            Error::op_invalid_args(format!("Invalid arg count in operation {:?}", op_type))
        })
    }

    /// Fills in auxiliary data if necessary/possible.
    fn fill_in_aux(op: Operation) -> Result<Operation> {
        use NativeOperation::{
            ContainerDeleteFromEntries, ContainerInsertFromEntries, ContainerUpdateFromEntries,
            ContainsFromEntries, NotContainsFromEntries,
        };
        use OperationAux as OpAux;
        use OperationType::Native;

        let op_type = &op.0;

        match (op_type, &op.2) {
            (Native(ContainsFromEntries), OpAux::None)
            | (Native(NotContainsFromEntries), OpAux::None) => {
                let container =
                    op.1.get(0)
                        .and_then(|arg| arg.value())
                        .ok_or(Error::custom(format!(
                            "Invalid container argument for op {}.",
                            op
                        )))?;
                let key =
                    op.1.get(1)
                        .and_then(|arg| arg.value())
                        .ok_or(Error::custom(format!(
                            "Invalid key argument for op {}.",
                            op
                        )))?;
                let proof = if op_type == &Native(ContainsFromEntries) {
                    container.prove_existence(key)?.1
                } else {
                    container.prove_nonexistence(key)?
                };
                Ok(Operation(op_type.clone(), op.1, OpAux::MerkleProof(proof)))
            }
            (Native(ContainerInsertFromEntries), OpAux::None)
            | (Native(ContainerUpdateFromEntries), OpAux::None)
            | (Native(ContainerDeleteFromEntries), OpAux::None) => {
                let old_container =
                    op.1.get(1)
                        .and_then(|arg| arg.value())
                        .ok_or(Error::custom(format!(
                            "Invalid container argument for op {}.",
                            op
                        )))?;
                let key =
                    op.1.get(2)
                        .and_then(|arg| arg.value())
                        .ok_or(Error::custom(format!(
                            "Invalid key argument for op {}.",
                            op
                        )))?;
                let value =
                    op.1.get(3)
                        .and_then(|arg| arg.value())
                        .ok_or(Error::custom(format!(
                            "Invalid key argument for op {}.",
                            op
                        )));
                let proof = match op_type {
                    Native(ContainerInsertFromEntries) => {
                        old_container.prove_insertion(key, value?)?
                    }
                    Native(ContainerUpdateFromEntries) => {
                        old_container.prove_update(key, value?)?
                    }
                    _ => old_container.prove_deletion(key)?,
                };
                Ok(Operation(
                    op_type.clone(),
                    op.1,
                    OpAux::MerkleTreeStateTransitionProof(proof),
                ))
            }
            _ => Ok(op),
        }
    }

    fn op_statement(
        &mut self,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        // Check for duplicate wildcard value assignments
        let mut uniq = HashSet::new();
        if !wildcard_values.iter().all(|(index, _)| uniq.insert(*index)) {
            return Err(Error::custom("duplicate wildcard value assignments"));
        }

        use NativeOperation::*;
        let st = match op.0 {
            OperationType::Native(o) => {
                let native_arg_error = move || Error::op_invalid_args(format!("{o:?}"));
                match (o, &op.1.as_slice(), &op.2) {
                    (None, &[], _) => Statement::None,
                    (EqualFromEntries, &[a1, a2], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        if v1 == v2 {
                            Statement::equal(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (NotEqualFromEntries, &[a1, a2], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        if v1 != v2 {
                            Statement::not_equal(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (LtFromEntries, &[a1, a2], _) => {
                        let (r1, v1) = a1.int_value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.int_value_and_ref().ok_or_else(native_arg_error)?;
                        if v1 < v2 {
                            Statement::lt(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (LtEqFromEntries, &[a1, a2], _) => {
                        let (r1, v1) = a1.int_value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.int_value_and_ref().ok_or_else(native_arg_error)?;
                        if v1 <= v2 {
                            Statement::lt_eq(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (CopyStatement, &[OperationArg::Statement(s)], _) => s.clone(),
                    (
                        TransitiveEqualFromStatements,
                        &[OperationArg::Statement(Statement::Equal(r1, r2)), OperationArg::Statement(Statement::Equal(r3, r4))],
                        _,
                    ) => {
                        if r2 == r3 {
                            Statement::Equal(r1.clone(), r4.clone())
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (LtToNotEqual, &[OperationArg::Statement(Statement::Lt(r1, r2))], _) => {
                        Statement::NotEqual(r1.clone(), r2.clone())
                    }
                    (SumOf, &[a1, a2, a3], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        if middleware::Operation::check_int_fn(v1, v2, v3, sum_op)? {
                            Statement::SumOf(r1, r2, r3)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (ProductOf, &[a1, a2, a3], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        if middleware::Operation::check_int_fn(v1, v2, v3, prod_op)? {
                            Statement::ProductOf(r1, r2, r3)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (MaxOf, &[a1, a2, a3], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        if middleware::Operation::check_int_fn(v1, v2, v3, max_op)? {
                            Statement::MaxOf(r1, r2, r3)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (HashOf, &[a1, a2, a3], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        if v1 == &hash_op(v2.clone(), v3.clone()) {
                            Statement::HashOf(r1, r2, r3)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (ContainsFromEntries, &[a1, a2, a3], _) => {
                        let (r1, _v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, _v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, _v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        // TODO: validate proof
                        Statement::Contains(r1, r2, r3)
                    }
                    (NotContainsFromEntries, &[a1, a2], _) => {
                        let (r1, _v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, _v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        // TODO: validate proof
                        Statement::NotContains(r1, r2)
                    }
                    (PublicKeyOf, &[a1, a2], _) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        if middleware::Operation::check_public_key(v1, v2)? {
                            Statement::PublicKeyOf(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (SignedBy, &[a1, a2], OperationAux::Signature(sig)) => {
                        let (r1, v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        if middleware::Operation::check_signed_by(v1, v2, sig)? {
                            Statement::SignedBy(r1, r2)
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                    (ContainerInsertFromEntries, &[a1, a2, a3, a4], _) => {
                        let (r1, _v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, _v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, _v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r4, _v4) = a4.value_and_ref().ok_or_else(native_arg_error)?;
                        // TODO: validate proof
                        Statement::ContainerInsert(r1, r2, r3, r4)
                    }
                    (ContainerUpdateFromEntries, &[a1, a2, a3, a4], _) => {
                        let (r1, _v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, _v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, _v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r4, _v4) = a4.value_and_ref().ok_or_else(native_arg_error)?;
                        // TODO: validate proof
                        Statement::ContainerUpdate(r1, r2, r3, r4)
                    }
                    (ContainerDeleteFromEntries, &[a1, a2, a3], _) => {
                        let (r1, _v1) = a1.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r2, _v2) = a2.value_and_ref().ok_or_else(native_arg_error)?;
                        let (r3, _v3) = a3.value_and_ref().ok_or_else(native_arg_error)?;
                        // TODO: validate proof
                        Statement::ContainerDelete(r1, r2, r3)
                    }
                    (t, _, _) => {
                        if t.is_syntactic_sugar() {
                            return Err(Error::custom(format!(
                                "Unexpected syntactic sugar: {:?}",
                                t
                            )));
                        } else {
                            return Err(native_arg_error());
                        }
                    }
                }
            }
            OperationType::Custom(cpr) => {
                let pred = &cpr.batch.predicates()[cpr.index];
                if pred.statements.len() != op.1.len() {
                    return Err(Error::custom(format!(
                        "Custom predicate operation needs {} statements but has {}.",
                        pred.statements.len(),
                        op.1.len()
                    )));
                }
                // All args should be statements to be pattern matched against statement templates.
                let args = op.1.iter().map(
                    |a| match a {
                        OperationArg::Statement(s) => Ok(s.clone()),
                        _ => Err(Error::custom(format!("Invalid argument {} to operation corresponding to custom predicate {:?}.", a, cpr)))
                    }
                ).collect::<Result<Vec<_>>>()?;

                let mut wildcard_map =
                    vec![Option::None; self.params.max_custom_predicate_wildcards];
                for (index, value) in wildcard_values.into_iter() {
                    if index >= wildcard_map.len() {
                        return Err(Error::custom(format!(
                            "wildcard index {} greater-equal than max {}",
                            index,
                            wildcard_map.len() - 1,
                        )));
                    }
                    wildcard_map[index] = Some(value);
                }
                for (st_tmpl, st) in pred.statements.iter().zip(args.iter()) {
                    let st_args = st.args();
                    for (st_tmpl_arg, st_arg) in st_tmpl.args.iter().zip(&st_args) {
                        if let Err(st_tmpl_check_error) =
                            check_st_tmpl(st_tmpl_arg, st_arg, &mut wildcard_map)
                        {
                            return Err(Error::statements_dont_match(
                                st.clone(),
                                st_tmpl.clone(),
                                wildcard_map,
                                st_tmpl_check_error,
                            ));
                        }
                    }
                }
                let v_default = Value::from(0);
                let st_args: Vec<_> = wildcard_map
                    .into_iter()
                    .take(pred.args_len)
                    .map(|v| v.unwrap_or_else(|| v_default.clone()))
                    .collect();
                check_custom_pred(&self.params, &cpr, &args, &st_args)?;
                Statement::Custom(cpr, st_args)
            }
        };
        Ok(st)
    }

    /// For every operation that has Entry statements as arguments we add a Contains statement to
    /// open the dictionary.
    fn add_entries_contains(&mut self, op: &Operation) -> Result<()> {
        for arg in &op.1 {
            if let OperationArg::Statement(Statement::Contains(
                ValueRef::Literal(dict),
                ValueRef::Literal(key),
                ValueRef::Literal(v),
            )) = arg
            {
                let root_key = (dict.clone(), key.clone());
                if !self.dict_contains.contains(&root_key) {
                    self.dict_contains.push(root_key);
                    self.priv_op(Operation::dict_contains(dict, key, v))?;
                }
            }
        }
        Ok(())
    }

    /// `wildcard_values`: wildcard values to use instead of EMPTY_VALUE for unresolved wildcards
    pub fn op(
        &mut self,
        public: bool,
        wildcard_values: Vec<(usize, Value)>,
        op: Operation,
    ) -> Result<Statement> {
        self.add_entries_contains(&op)?;
        let op = Self::fill_in_aux(Self::lower_op(op)?)?;
        let st = self.op_statement(wildcard_values, op.clone())?;
        self.insert(public, (st, op))?;

        Ok(self.statements[self.statements.len() - 1].clone())
    }

    pub fn reveal(&mut self, st: &Statement) {
        self.public_statements.push(st.clone());
    }

    pub fn prove(&self, prover: &dyn MainPodProver) -> Result<MainPod> {
        let compiler = MainPodCompiler::new(&self.params);
        let inputs = MainPodCompilerInputs {
            statements: &self.statements,
            operations: &self.operations,
            public_statements: &self.public_statements,
        };

        let (statements, operations, public_statements) = compiler.compile(inputs, &self.params)?;

        let inputs = MainPodInputs {
            pods: &self.input_pods.iter().map(|p| p.pod.as_ref()).collect_vec(),
            statements: &statements,
            operations: &operations,
            public_statements: &public_statements,
            vd_set: self.vd_set.clone(),
        };
        let pod = prover.prove(&self.params, inputs)?;

        Ok(MainPod {
            pod,
            params: self.params.clone(),
            public_statements: self.public_statements.clone(),
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(try_from = "SerializedMainPod", into = "SerializedMainPod")]
pub struct MainPod {
    pub pod: Box<dyn middleware::Pod>,
    pub public_statements: Vec<Statement>,
    pub params: Params,
}

impl fmt::Display for MainPod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MainPod: {}", self.pod.statements_hash())?;
        writeln!(f, "  valid?  {}", self.pod.verify().is_ok())?;
        writeln!(f, "  statements:")?;
        for st in &self.pod.pub_statements() {
            writeln!(f, "    - {}", st)?;
        }
        Ok(())
    }
}

impl MainPod {
    pub fn statements_hash(&self) -> Hash {
        self.pod.statements_hash()
    }
}

struct MainPodCompilerInputs<'a> {
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
            OperationArg::Literal(_v) => Some(Statement::None),
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
        Ok(middleware::Operation::op(op.0.clone(), &mop_args, &op.2)?)
    }

    fn compile_st_op(&mut self, st: &Statement, op: &Operation, params: &Params) -> Result<()> {
        let middle_op = self.compile_op(op)?;
        let is_correct = middle_op.check(params, st)?;
        if !is_correct {
            // todo: improve error handling
            Err(Error::custom(format!(
                "Compile failed due to invalid deduction:\n {} ⇏ {}",
                middle_op, st
            )))
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

#[cfg(test)]
pub mod tests {

    use num::BigUint;

    use super::*;
    use crate::{
        backends::plonky2::{
            mock::mainpod::MockProver, primitives::ec::schnorr::SecretKey, signer::Signer,
        },
        dict,
        examples::{
            attest_eth_friend, custom::eth_dos_request, great_boy_pod_full_flow,
            tickets_pod_full_flow, zu_kyc_pod_builder, zu_kyc_pod_request,
            zu_kyc_sign_dict_builders, EthDosHelper, MOCK_VD_SET,
        },
        lang::parse,
        middleware::{
            containers::{Array, Set},
            Signer as _, Value,
        },
    };

    // Check that frontend public statements agree with those
    // embedded in a MainPod.
    fn check_public_statements(pod: &MainPod) -> Result<()> {
        std::iter::zip(pod.public_statements.clone(), pod.pod.pub_statements())
            .for_each(|(fes, s)| assert_eq!(fes, s));
        Ok(())
    }

    #[test]
    fn test_front_zu_kyc() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let (gov_id, pay_stub) = zu_kyc_sign_dict_builders(&params);

        println!("{}", gov_id);
        println!("{}", pay_stub);

        let gov_id_signer = Signer(SecretKey(1u32.into()));
        let gov_id = gov_id.sign(&gov_id_signer)?;
        println!("{}", gov_id);

        let pay_stub_signer = Signer(SecretKey(2u32.into()));
        let pay_stub = pay_stub.sign(&pay_stub_signer)?;
        println!("{}", pay_stub);

        let kyc_builder = zu_kyc_pod_builder(&params, vd_set, &gov_id, &pay_stub)?;
        println!("{}", kyc_builder);

        // prove kyc with MockProver and print it
        let prover = MockProver {};
        let kyc = kyc_builder.prove(&prover)?;

        println!("{}", kyc);

        kyc.pod.verify()?;

        let request = zu_kyc_pod_request(
            &Value::from(gov_id_signer.public_key()),
            &Value::from(pay_stub_signer.public_key()),
        )?;
        // Check the bindings of the "gov" and "pay" wildcards from the PodRequest
        let bindings = request.exact_match_pod(&*kyc.pod).unwrap();
        assert_eq!(
            *bindings.get("gov").unwrap(),
            gov_id.dict.commitment().into()
        );
        assert_eq!(
            *bindings.get("pay").unwrap(),
            pay_stub.dict.commitment().into()
        );

        check_public_statements(&kyc)
    }

    #[test]
    fn test_ethdos_recursive() -> Result<()> {
        let params = Params {
            max_input_pods_public_statements: 8,
            max_statements: 24,
            max_public_statements: 8,
            ..Default::default()
        };
        let vd_set = &*MOCK_VD_SET;

        let alice = Signer(SecretKey(1u32.into()));
        let bob = Signer(SecretKey(2u32.into()));
        let charlie = Signer(SecretKey(3u32.into()));
        let david = Signer(SecretKey(4u32.into()));

        let helper = EthDosHelper::new(&params, vd_set, alice.public_key())?;

        let prover = MockProver {};

        let alice_attestation = attest_eth_friend(&params, &alice, bob.public_key());
        let dist_1 = helper.dist_1(&alice_attestation)?.prove(&prover)?;
        dist_1.pod.verify()?;
        let request = eth_dos_request()?;
        assert!(request.exact_match_pod(&*dist_1.pod).is_ok());
        let bindings = request.exact_match_pod(&*dist_1.pod).unwrap();
        assert_eq!(*bindings.get("src").unwrap(), alice.public_key().into());
        assert_eq!(*bindings.get("dst").unwrap(), bob.public_key().into());
        assert_eq!(*bindings.get("distance").unwrap(), 1.into());

        let bob_attestation = attest_eth_friend(&params, &bob, charlie.public_key());
        let dist_2 = helper
            .dist_n_plus_1(&dist_1, &bob_attestation)?
            .prove(&prover)?;
        dist_2.pod.verify()?;
        assert!(request.exact_match_pod(&*dist_2.pod).is_ok());
        let bindings = request.exact_match_pod(&*dist_2.pod).unwrap();
        assert_eq!(*bindings.get("src").unwrap(), alice.public_key().into());
        assert_eq!(*bindings.get("dst").unwrap(), charlie.public_key().into());
        assert_eq!(*bindings.get("distance").unwrap(), 2.into());

        let charlie_attestation = attest_eth_friend(&params, &charlie, david.public_key());
        let dist_3 = helper
            .dist_n_plus_1(&dist_2, &charlie_attestation)?
            .prove(&prover)?;
        dist_3.pod.verify()?;
        assert!(request.exact_match_pod(&*dist_3.pod).is_ok());
        let bindings = request.exact_match_pod(&*dist_3.pod).unwrap();
        assert_eq!(*bindings.get("src").unwrap(), alice.public_key().into());
        assert_eq!(*bindings.get("dst").unwrap(), david.public_key().into());
        assert_eq!(*bindings.get("distance").unwrap(), 3.into());

        Ok(())
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
        let builder = tickets_pod_full_flow(&Params::default(), &MOCK_VD_SET)?;
        println!("{}", builder);

        Ok(())
    }

    #[test]
    // Transitive equality not implemented yet
    #[should_panic]
    fn test_equal() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let mut signed_builder = SignedDictBuilder::new(&params);
        signed_builder.insert("a", 1);
        signed_builder.insert("b", 1);
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = signed_builder.sign(&signer).unwrap();

        let mut builder = MainPodBuilder::new(&params, vd_set);
        builder
            .pub_op(Operation::dict_signed_by(&signed_dict))
            .unwrap();

        let op_eq1 = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::from((&signed_dict, "a")),
                OperationArg::from((&signed_dict, "b")),
            ],
            OperationAux::None,
        );
        let st1 = builder.op(true, vec![], op_eq1).unwrap();
        let op_eq2 = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::from((&signed_dict, "b")),
                OperationArg::from((&signed_dict, "a")),
            ],
            OperationAux::None,
        );
        let st2 = builder.op(true, vec![], op_eq2).unwrap();

        let op_eq3 = Operation(
            OperationType::Native(NativeOperation::TransitiveEqualFromStatements),
            vec![OperationArg::Statement(st1), OperationArg::Statement(st2)],
            OperationAux::None,
        );
        builder.op(true, vec![], op_eq3).unwrap();

        let prover = MockProver {};
        let pod = builder.prove(&prover).unwrap();

        println!("{}", pod);
    }

    #[test]
    #[should_panic]
    fn test_false_st() {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = SignedDictBuilder::new(&params);

        builder.insert("num", 2);
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = builder.sign(&signer).unwrap();

        println!("{}", signed_dict);

        let mut builder = MainPodBuilder::new(&params, vd_set);
        builder
            .pub_op(Operation::dict_signed_by(&signed_dict))
            .unwrap();
        builder
            .pub_op(Operation::gt((&signed_dict, "num"), 5))
            .unwrap();

        let prover = MockProver {};
        let false_pod = builder.prove(&prover).unwrap();

        println!("{}", builder);
        println!("{}", false_pod);
    }

    #[test]
    fn test_dictionaries() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = SignedDictBuilder::new(&params);

        let dict = dict!({
            "a" => 1,
            "b" => 2,
            "c" => 3,
        });
        let dict_root = Value::from(dict.clone());
        builder.insert("dict", dict_root);

        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = builder.sign(&signer).unwrap();

        let mut builder = MainPodBuilder::new(&params, vd_set);
        builder
            .pub_op(Operation::dict_signed_by(&signed_dict))
            .unwrap();
        let st0 = signed_dict.get_statement("dict").unwrap();
        let local = dict!({"key" => "a"});
        let st1 = builder
            .op(true, vec![], Operation::dict_contains(local, "key", "a"))
            .unwrap();

        builder.pub_op(Operation(
            // OperationType
            OperationType::Native(NativeOperation::DictContainsFromEntries),
            // Vec<OperationArg>
            vec![
                OperationArg::Statement(st0.clone()),
                OperationArg::Statement(st1),
                OperationArg::Literal(Value::from(1)),
            ],
            OperationAux::MerkleProof(dict.prove(&Key::from("a")).unwrap().1),
        ))?;

        let mut new_dict = dict.clone();
        new_dict.insert(&Key::from("d"), &Value::from(4))?;

        builder.pub_op(Operation(
            OperationType::Native(NativeOperation::DictInsertFromEntries),
            vec![
                Value::from(new_dict.clone()).into(),
                OperationArg::Statement(st0.clone()),
                "d".into(),
                4.into(),
            ],
            OperationAux::None,
        ))?;

        let mut new_old_dict = new_dict.clone();
        new_old_dict.delete(&Key::from("d"))?;

        assert_eq!(new_old_dict, dict);

        builder.pub_op(Operation(
            OperationType::Native(NativeOperation::DictDeleteFromEntries),
            vec![
                OperationArg::Statement(st0.clone()),
                Value::from(new_dict).into(),
                "d".into(),
            ],
            OperationAux::None,
        ))?;

        new_old_dict.update(&Key::from("c"), &55.into())?;

        builder.pub_op(Operation(
            OperationType::Native(NativeOperation::DictUpdateFromEntries),
            vec![
                Value::from(new_old_dict).into(),
                OperationArg::Statement(st0.clone()),
                "c".into(),
                55.into(),
            ],
            OperationAux::None,
        ))?;

        let main_prover = MockProver {};
        let main_pod = builder.prove(&main_prover).unwrap();

        println!("{}", main_pod);

        Ok(())
    }

    #[test]
    fn test_sets() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = MainPodBuilder::new(&params, vd_set);

        let empty_set = Set::new([].into());

        let mut set1 = empty_set.clone();
        set1.insert(&1.into())?;

        let mut set2 = set1.clone();
        set2.delete(&1.into())?;

        assert_eq!(set2, empty_set);

        builder.pub_op(Operation(
            // OperationType
            OperationType::Native(NativeOperation::SetInsertFromEntries),
            // Vec<OperationArg>
            vec![
                Value::from(set1.clone()).into(),
                Value::from(empty_set.clone()).into(),
                1.into(),
            ],
            OperationAux::None,
        ))?;

        builder.pub_op(Operation(
            // OperationType
            OperationType::Native(NativeOperation::SetDeleteFromEntries),
            // Vec<OperationArg>
            vec![
                Value::from(empty_set.clone()).into(),
                Value::from(set1.clone()).into(),
                1.into(),
            ],
            OperationAux::None,
        ))?;

        let main_prover = MockProver {};
        let main_pod = builder.prove(&main_prover).unwrap();

        println!("{}", main_pod);

        Ok(())
    }

    #[test]
    fn test_arrays() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = MainPodBuilder::new(&params, vd_set);

        let array1 = Array::new([1.into()].into());

        let mut array2 = array1.clone();
        array2.update(0, &5.into())?;

        builder.pub_op(Operation(
            // OperationType
            OperationType::Native(NativeOperation::ArrayUpdateFromEntries),
            // Vec<OperationArg>
            vec![
                Value::from(array2.clone()).into(),
                Value::from(array1.clone()).into(),
                0.into(),
                5.into(),
            ],
            OperationAux::None,
        ))?;

        let main_prover = MockProver {};
        let main_pod = builder.prove(&main_prover).unwrap();

        println!("{}", main_pod);

        Ok(())
    }

    #[test]
    fn test_public_key_of() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let sk = SecretKey::new_rand();
        let pk = sk.public_key();

        // Signed Dict contains public key as owner
        let mut builder = SignedDictBuilder::new(&params);
        builder.insert("owner", Value::from(pk));
        builder.insert("other_data", Value::from(123));
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = builder.sign(&signer).unwrap();

        // Main POD proves ownership of the owner's secret key.
        let mut builder = MainPodBuilder::new(&params, vd_set);
        builder.pub_op(Operation::signed_by(
            Value::from(signed_dict.dict.clone()),
            Value::from(signed_dict.public_key),
            signed_dict.signature.clone(),
        ))?;

        let st0 = builder.priv_op(Operation::dict_contains(
            signed_dict.dict,
            "owner",
            Value::from(pk),
        ))?;
        let local = dict!({ "known_secret" => sk.clone() });
        let st1 = builder.priv_op(Operation::dict_contains(
            local,
            "known_secret",
            Value::from(sk),
        ))?;
        builder
            .pub_op(Operation(
                OperationType::Native(NativeOperation::PublicKeyOf),
                vec![OperationArg::Statement(st0), OperationArg::Statement(st1)],
                OperationAux::None,
            ))
            .unwrap();

        // Prove Main POD to check.
        let main_prover = MockProver {};
        let main_pod = builder.prove(&main_prover).unwrap();

        println!("{}", main_pod);

        Ok(())
    }

    #[test]
    fn test_public_key_of_wrong_key() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let sk = SecretKey::new_rand();
        let pk = sk.public_key();

        // Signed POD contains public key as owner
        let mut builder = SignedDictBuilder::new(&params);
        builder.insert("owner", Value::from(pk));
        builder.insert("other_data", Value::from(123));
        let signer = Signer(SecretKey(1u32.into()));
        let signed_dict = builder.sign(&signer).unwrap();

        // Try to build with the wrong secret key.  The pre-proving checks
        // will catch this.
        let mut builder = MainPodBuilder::new(&params, vd_set);
        builder
            .pub_op(Operation::dict_signed_by(&signed_dict))
            .unwrap();
        let st0 = signed_dict.get_statement("owner").unwrap();
        let local = dict!({"known_secret" => SecretKey(BigUint::from(123u32))});
        let st1 = builder
            .op(
                true,
                vec![],
                Operation::dict_contains(local, "known_secret", SecretKey(BigUint::from(123u32))),
            )
            .unwrap();
        assert!(builder
            .pub_op(Operation(
                // OperationType
                OperationType::Native(NativeOperation::PublicKeyOf),
                // Vec<OperationArg>
                vec![OperationArg::Statement(st0), OperationArg::Statement(st1)],
                OperationAux::None,
            ))
            .is_err());

        Ok(())
    }

    #[test]
    fn test_public_key_of_wrong_type() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let sk = SecretKey::new_rand();
        let pk = sk.public_key();

        // Try to build with wrong type in 1st arg
        let mut builder = MainPodBuilder::new(&params, vd_set);
        let int2 = Value::from(123);
        let sk = Value::from(sk);
        assert!(builder
            .pub_op(Operation(
                // OperationType
                OperationType::Native(NativeOperation::PublicKeyOf),
                // Vec<OperationArg>
                vec![OperationArg::Literal(int2), OperationArg::Literal(sk),],
                OperationAux::None,
            ))
            .is_err());

        // Try to build with wrong type in 2nd arg
        let mut builder = MainPodBuilder::new(&params, vd_set);
        let pk = Value::from(pk);
        let int1 = Value::from(123);
        assert!(builder
            .pub_op(Operation(
                // OperationType
                OperationType::Native(NativeOperation::PublicKeyOf),
                // Vec<OperationArg>
                vec![
                    OperationArg::Literal(pk.clone()),
                    OperationArg::Literal(int1),
                ],
                OperationAux::None,
            ))
            .is_err());

        Ok(())
    }

    #[should_panic]
    #[test]
    fn test_reject_unsound_statement() {
        // try to insert a statement that doesn't follow from the operation
        // right now the mock prover catches this when it calls compile()
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;
        let mut builder = MainPodBuilder::new(&params, vd_set);
        let local = dict!({"a" => 3, "b" => 27});
        let value_of_a = Statement::contains(local.clone(), "a", 3);
        let value_of_b = Statement::contains(local.clone(), "b", 27);

        let op_contains = Operation(
            OperationType::Native(NativeOperation::DictContainsFromEntries),
            vec![],
            OperationAux::None,
        );
        builder
            .insert(false, (value_of_a.clone(), op_contains.clone()))
            .unwrap();
        builder
            .insert(false, (value_of_b.clone(), op_contains))
            .unwrap();
        let st = Statement::equal(
            AnchoredKey::from((&local, "a")),
            AnchoredKey::from((&local, "b")),
        );
        let op = Operation(
            OperationType::Native(NativeOperation::EqualFromEntries),
            vec![
                OperationArg::Statement(value_of_a),
                OperationArg::Statement(value_of_b),
            ],
            OperationAux::None,
        );
        builder.insert(false, (st, op)).unwrap();

        let prover = MockProver {};
        let pod = builder.prove(&prover).unwrap();
        pod.pod.verify().unwrap();
    }

    #[test]
    fn test_wildcard_values() -> Result<()> {
        let params = Params::default();
        let vd_set = &*MOCK_VD_SET;

        let input = r#"
        Test(a, b) = OR(
            Equal(a, 5)
            Equal(b, 5)
        )
        "#;
        let batch = parse(input, &params, &[]).unwrap().custom_batch;
        let pred_test = batch.predicate_ref_by_name("Test").unwrap();

        // Try to build with wrong type in 1st arg
        let mut builder = MainPodBuilder::new(&params, vd_set);
        let st0 = builder.priv_op(Operation::eq(5, 5)).unwrap();
        let wildcard_values = vec![(1, Value::from(42))];
        let st = builder
            .op(
                true,
                wildcard_values,
                Operation::custom(pred_test, [st0, Statement::None]),
            )
            .unwrap();
        let st_args = st.args();
        assert_eq!(StatementArg::Literal(Value::from(5)), st_args[0]);
        assert_eq!(StatementArg::Literal(Value::from(42)), st_args[1]);

        let prover = MockProver {};
        let pod = builder.prove(&prover).unwrap();
        pod.pod.verify().unwrap();

        Ok(())
    }
}
