use std::{fmt, iter};

use log::error;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::primitives::{
        ec::{
            curve::{Point as PublicKey, GROUP_ORDER},
            schnorr::SecretKey,
        },
        merkletree::{MerkleProof, MerkleTree},
    },
    middleware::{
        hash_values, AnchoredKey, CustomPredicate, CustomPredicateRef, Error, NativePredicate,
        Params, Predicate, Result, Statement, StatementArg, StatementTmplArg, ToFields, Value,
        ValueRef, Wildcard, F, SELF,
    },
};

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum OperationType {
    Native(NativeOperation),
    Custom(CustomPredicateRef),
}

#[derive(Clone, Debug, PartialEq)]
pub enum OperationAux {
    None,
    MerkleProof(MerkleProof),
}

impl fmt::Display for OperationAux {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::None => write!(f, "<no aux>")?,
            Self::MerkleProof(pf) => write!(f, "merkle_proof({})", pf)?,
        }
        Ok(())
    }
}

impl ToFields for OperationType {
    /// Encoding:
    /// - Native(native_op) => [1, [native_op], 0, 0, 0, 0]
    /// - Custom(batch, index) => [3, [batch.id], index]
    fn to_fields(&self, params: &Params) -> Vec<F> {
        let mut fields: Vec<F> = match self {
            Self::Native(p) => iter::once(F::from_canonical_u64(1))
                .chain(p.to_fields(params))
                .collect(),
            Self::Custom(CustomPredicateRef { batch, index }) => {
                iter::once(F::from_canonical_u64(3))
                    .chain(batch.id().0)
                    .chain(iter::once(F::from_canonical_usize(*index)))
                    .collect()
            }
        };
        fields.resize_with(Params::operation_type_size(), || F::from_canonical_u64(0));
        fields
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NativeOperation {
    None = 0,
    NewEntry = 1,
    CopyStatement = 2,
    EqualFromEntries = 3,
    NotEqualFromEntries = 4,
    LtEqFromEntries = 5,
    LtFromEntries = 6,
    TransitiveEqualFromStatements = 7,
    LtToNotEqual = 8,
    ContainsFromEntries = 9,
    NotContainsFromEntries = 10,
    SumOf = 11,
    ProductOf = 12,
    MaxOf = 13,
    HashOf = 14,
    PublicKeyOf = 15,

    // Syntactic sugar operations.  These operations are not supported by the backend.  The
    // frontend compiler is responsible of translating these operations into the operations above.
    DictContainsFromEntries = 1001,
    DictNotContainsFromEntries = 1002,
    SetContainsFromEntries = 1003,
    SetNotContainsFromEntries = 1004,
    ArrayContainsFromEntries = 1005,
    GtEqFromEntries = 1006,
    GtFromEntries = 1007,
    GtToNotEqual = 1008,
}

impl NativeOperation {
    pub fn is_syntactic_sugar(self) -> bool {
        (self as usize) >= 1000
    }
}

impl ToFields for NativeOperation {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        vec![F::from_canonical_u64(*self as u64)]
    }
}

impl OperationType {
    /// Gives the type of predicate that the operation will output, if known.
    /// CopyStatement may output any predicate (it will match the statement copied),
    /// so output_predicate returns None on CopyStatement.
    pub fn output_predicate(&self) -> Option<Predicate> {
        match self {
            OperationType::Native(native_op) => match native_op {
                NativeOperation::None => Some(Predicate::Native(NativePredicate::None)),
                NativeOperation::NewEntry => Some(Predicate::Native(NativePredicate::Equal)),
                NativeOperation::CopyStatement => None,
                NativeOperation::EqualFromEntries => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::NotEqualFromEntries => {
                    Some(Predicate::Native(NativePredicate::NotEqual))
                }
                NativeOperation::LtEqFromEntries => Some(Predicate::Native(NativePredicate::LtEq)),
                NativeOperation::LtFromEntries => Some(Predicate::Native(NativePredicate::Lt)),
                NativeOperation::TransitiveEqualFromStatements => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::LtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::ContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::Contains))
                }
                NativeOperation::NotContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::NotContains))
                }
                NativeOperation::SumOf => Some(Predicate::Native(NativePredicate::SumOf)),
                NativeOperation::ProductOf => Some(Predicate::Native(NativePredicate::ProductOf)),
                NativeOperation::MaxOf => Some(Predicate::Native(NativePredicate::MaxOf)),
                NativeOperation::HashOf => Some(Predicate::Native(NativePredicate::HashOf)),
                NativeOperation::PublicKeyOf => {
                    Some(Predicate::Native(NativePredicate::PublicKeyOf))
                }
                no => unreachable!("Unexpected syntactic sugar op {:?}", no),
            },
            OperationType::Custom(cpr) => Some(Predicate::Custom(cpr.clone())),
        }
    }
}

// TODO: Refine this enum.
#[derive(Clone, Debug, PartialEq)]
pub enum Operation {
    None,
    NewEntry,
    CopyStatement(Statement),
    EqualFromEntries(Statement, Statement),
    NotEqualFromEntries(Statement, Statement),
    LtEqFromEntries(Statement, Statement),
    LtFromEntries(Statement, Statement),
    TransitiveEqualFromStatements(Statement, Statement),
    LtToNotEqual(Statement),
    ContainsFromEntries(
        /* root  */ Statement,
        /* key   */ Statement,
        /* value */ Statement,
        /* proof */ MerkleProof,
    ),
    NotContainsFromEntries(
        /* root  */ Statement,
        /* key   */ Statement,
        /* proof */ MerkleProof,
    ),
    SumOf(Statement, Statement, Statement),
    ProductOf(Statement, Statement, Statement),
    MaxOf(Statement, Statement, Statement),
    HashOf(Statement, Statement, Statement),
    PublicKeyOf(Statement, Statement),
    Custom(CustomPredicateRef, Vec<Statement>),
}

pub(crate) fn sum_op(x: i64, y: i64) -> i64 {
    x + y
}

pub(crate) fn prod_op(x: i64, y: i64) -> i64 {
    x * y
}

pub(crate) fn max_op(x: i64, y: i64) -> i64 {
    x.max(y)
}

pub(crate) fn hash_op(x: Value, y: Value) -> Value {
    Value::from(hash_values(&[x, y]))
}

impl Operation {
    pub fn op_type(&self) -> OperationType {
        type OT = OperationType;
        use NativeOperation::*;
        match self {
            Self::None => OT::Native(None),
            Self::NewEntry => OT::Native(NewEntry),
            Self::CopyStatement(_) => OT::Native(CopyStatement),
            Self::EqualFromEntries(_, _) => OT::Native(EqualFromEntries),
            Self::NotEqualFromEntries(_, _) => OT::Native(NotEqualFromEntries),
            Self::LtEqFromEntries(_, _) => OT::Native(LtEqFromEntries),
            Self::LtFromEntries(_, _) => OT::Native(LtFromEntries),
            Self::TransitiveEqualFromStatements(_, _) => OT::Native(TransitiveEqualFromStatements),
            Self::LtToNotEqual(_) => OT::Native(LtToNotEqual),
            Self::ContainsFromEntries(_, _, _, _) => OT::Native(ContainsFromEntries),
            Self::NotContainsFromEntries(_, _, _) => OT::Native(NotContainsFromEntries),
            Self::SumOf(_, _, _) => OT::Native(SumOf),
            Self::ProductOf(_, _, _) => OT::Native(ProductOf),
            Self::MaxOf(_, _, _) => OT::Native(MaxOf),
            Self::HashOf(_, _, _) => OT::Native(HashOf),
            Self::PublicKeyOf(_, _) => OT::Native(PublicKeyOf),
            Self::Custom(cpr, _) => OT::Custom(cpr.clone()),
        }
    }

    pub fn args(&self) -> Vec<Statement> {
        match self.clone() {
            Self::None => vec![],
            Self::NewEntry => vec![],
            Self::CopyStatement(s) => vec![s],
            Self::EqualFromEntries(s1, s2) => vec![s1, s2],
            Self::NotEqualFromEntries(s1, s2) => vec![s1, s2],
            Self::LtEqFromEntries(s1, s2) => vec![s1, s2],
            Self::LtFromEntries(s1, s2) => vec![s1, s2],
            Self::TransitiveEqualFromStatements(s1, s2) => vec![s1, s2],
            Self::LtToNotEqual(s) => vec![s],
            Self::ContainsFromEntries(s1, s2, s3, _pf) => vec![s1, s2, s3],
            Self::NotContainsFromEntries(s1, s2, _pf) => vec![s1, s2],
            Self::SumOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::ProductOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::MaxOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::HashOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::PublicKeyOf(s1, s2) => vec![s1, s2],
            Self::Custom(_, args) => args,
        }
    }

    /// Extracts auxiliary data from operation.
    pub fn aux(&self) -> OperationAux {
        match self {
            Self::ContainsFromEntries(_, _, _, mp) => OperationAux::MerkleProof(mp.clone()),
            Self::NotContainsFromEntries(_, _, mp) => OperationAux::MerkleProof(mp.clone()),
            _ => OperationAux::None,
        }
    }

    /// Forms operation from op-code and arguments.
    pub fn op(op_code: OperationType, args: &[Statement], aux: &OperationAux) -> Result<Self> {
        type OA = OperationAux;
        type NO = NativeOperation;
        Ok(match op_code {
            OperationType::Native(o) => match (o, &args, aux.clone()) {
                (NO::None, &[], OA::None) => Self::None,
                (NO::NewEntry, &[], OA::None) => Self::NewEntry,
                (NO::CopyStatement, &[s], OA::None) => Self::CopyStatement(s.clone()),
                (NO::EqualFromEntries, &[s1, s2], OA::None) => {
                    Self::EqualFromEntries(s1.clone(), s2.clone())
                }
                (NO::NotEqualFromEntries, &[s1, s2], OA::None) => {
                    Self::NotEqualFromEntries(s1.clone(), s2.clone())
                }
                (NO::LtEqFromEntries, &[s1, s2], OA::None) => {
                    Self::LtEqFromEntries(s1.clone(), s2.clone())
                }
                (NO::LtFromEntries, &[s1, s2], OA::None) => {
                    Self::LtFromEntries(s1.clone(), s2.clone())
                }
                (NO::ContainsFromEntries, &[s1, s2, s3], OA::MerkleProof(pf)) => {
                    Self::ContainsFromEntries(s1.clone(), s2.clone(), s3.clone(), pf)
                }
                (NO::NotContainsFromEntries, &[s1, s2], OA::MerkleProof(pf)) => {
                    Self::NotContainsFromEntries(s1.clone(), s2.clone(), pf)
                }
                (NO::SumOf, &[s1, s2, s3], OA::None) => {
                    Self::SumOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::ProductOf, &[s1, s2, s3], OA::None) => {
                    Self::ProductOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::MaxOf, &[s1, s2, s3], OA::None) => {
                    Self::MaxOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::HashOf, &[s1, s2, s3], OA::None) => {
                    Self::HashOf(s1.clone(), s2.clone(), s3.clone())
                }
                (NO::PublicKeyOf, &[s1, s2], OA::None) => Self::PublicKeyOf(s1.clone(), s2.clone()),
                _ => Err(Error::custom(format!(
                    "Ill-formed operation {:?} with {} arguments {:?} and aux {:?}.",
                    op_code,
                    args.len(),
                    args,
                    aux
                )))?,
            },
            OperationType::Custom(cpr) => Self::Custom(cpr, args.to_vec()),
        })
    }

    /// Checks the given operation against a statement, and prints information if the check does not pass
    pub fn check_and_log(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        let valid: bool = self.check(params, output_statement)?;
        if !valid {
            error!("Check failed on the following statement");
            error!("{}", output_statement);
        }
        Ok(valid)
    }

    pub(crate) fn check_int_fn(
        v1: &Value,
        v2: &Value,
        v3: &Value,
        f: impl FnOnce(i64, i64) -> i64,
    ) -> Result<bool> {
        let i1: i64 = v1.typed().try_into()?;
        let i2: i64 = v2.typed().try_into()?;
        let i3: i64 = v3.typed().try_into()?;
        Ok(i1 == f(i2, i3))
    }

    pub(crate) fn check_public_key(v1: &Value, v2: &Value) -> Result<bool> {
        let pk: PublicKey = v1.typed().try_into()?;
        let sk: SecretKey = v2.typed().try_into()?;
        Ok(sk.0 < *GROUP_ORDER && pk == sk.public_key())
    }

    /// Checks the given operation against a statement.
    pub fn check(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        use Statement::*;
        let deduction_err = || Error::invalid_deduction(self.clone(), output_statement.clone());
        let val = |v, s| value_from_op(s, v).ok_or_else(deduction_err);
        let b = match (self, output_statement) {
            (Self::None, None) => true,
            (Self::NewEntry, Equal(ValueRef::Key(AnchoredKey { pod_id, .. }), _)) => {
                pod_id == &SELF
            }
            (Self::CopyStatement(s1), s2) => s1 == s2,
            (Self::EqualFromEntries(s1, s2), Equal(v3, v4)) => val(v3, s1)? == val(v4, s2)?,
            (Self::NotEqualFromEntries(s1, s2), NotEqual(v3, v4)) => val(v3, s1)? != val(v4, s2)?,
            (Self::LtEqFromEntries(s1, s2), LtEq(v3, v4)) => val(v3, s1)? <= val(v4, s2)?,
            (Self::LtFromEntries(s1, s2), Lt(v3, v4)) => val(v3, s1)? < val(v4, s2)?,
            (
                Self::ContainsFromEntries(root_s, key_s, val_s, pf),
                Contains(root_v, key_v, val_v),
            ) => {
                let root = val(root_v, root_s)?;
                let key = val(key_v, key_s)?;
                let value = val(val_v, val_s)?;
                MerkleTree::verify(
                    params.max_depth_mt_containers,
                    root.raw().into(),
                    pf,
                    &key.raw(),
                    &value.raw(),
                )?;
                true
            }
            (Self::NotContainsFromEntries(root_s, key_s, pf), NotContains(root_v, key_v)) => {
                let root = val(root_v, root_s)?;
                let key = val(key_v, key_s)?;
                MerkleTree::verify_nonexistence(
                    params.max_depth_mt_containers,
                    root.raw().into(),
                    pf,
                    &key.raw(),
                )?;
                true
            }
            (
                Self::TransitiveEqualFromStatements(Equal(ak1, ak2), Equal(ak3, ak4)),
                Equal(ak5, ak6),
            ) => ak2 == ak3 && ak5 == ak1 && ak6 == ak4,
            (Self::LtToNotEqual(Lt(ak1, ak2)), NotEqual(ak3, ak4)) => ak1 == ak3 && ak2 == ak4,
            (Self::SumOf(s1, s2, s3), SumOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, sum_op)?
            }
            (Self::ProductOf(s1, s2, s3), ProductOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, prod_op)?
            }
            (Self::MaxOf(s1, s2, s3), MaxOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, max_op)?
            }
            (Self::HashOf(s1, s2, s3), HashOf(v4, v5, v6)) => {
                val(v4, s1)? == hash_op(val(v5, s2)?, val(v6, s3)?)
            }
            (Self::PublicKeyOf(s1, s2), PublicKeyOf(v3, v4)) => {
                Self::check_public_key(&val(v3, s1)?, &val(v4, s2)?)?
            }
            (Self::Custom(CustomPredicateRef { batch, index }, args), Custom(cpr, s_args))
                if batch == &cpr.batch && index == &cpr.index =>
            {
                check_custom_pred(params, cpr, args, s_args).map(|_| true)?
            }
            _ => return Err(deduction_err()),
        };
        Ok(b)
    }
}

/// Check that a StatementArg follows a StatementTmplArg based on the currently mapped wildcards.
/// Update the wildcard map with newly found wildcards.
pub fn check_st_tmpl(
    st_tmpl_arg: &StatementTmplArg,
    st_arg: &StatementArg,
    // Map from wildcards to values that we have seen so far.
    wildcard_map: &mut [Option<Value>],
) -> Result<()> {
    // Check that the value `v` at wildcard `wc` exists in the map or set it.
    fn check_or_set(v: Value, wc: &Wildcard, wildcard_map: &mut [Option<Value>]) -> Result<()> {
        if let Some(prev) = &wildcard_map[wc.index] {
            if *prev != v {
                return Err(Error::invalid_wildcard_assignment(
                    wc.clone(),
                    v,
                    prev.clone(),
                ));
            }
        } else {
            wildcard_map[wc.index] = Some(v);
        }
        Ok(())
    }

    match (st_tmpl_arg, st_arg) {
        (StatementTmplArg::None, StatementArg::None) => Ok(()),
        (StatementTmplArg::Literal(lhs), StatementArg::Literal(rhs)) if lhs == rhs => Ok(()),
        (
            StatementTmplArg::AnchoredKey(pod_id_wc, key_tmpl),
            StatementArg::Key(AnchoredKey { pod_id, key }),
        ) => {
            let pod_id_ok = check_or_set(Value::from(*pod_id), pod_id_wc, wildcard_map);
            pod_id_ok.and_then(|_| {
                (key_tmpl == key).then_some(()).ok_or(
                    Error::mismatched_anchored_key_in_statement_tmpl_arg(
                        pod_id_wc.clone(),
                        *pod_id,
                        key_tmpl.clone(),
                        key.clone(),
                    ),
                )
            })
        }
        (StatementTmplArg::Wildcard(wc), StatementArg::Literal(v)) => {
            check_or_set(v.clone(), wc, wildcard_map)
        }
        _ => Err(Error::mismatched_statement_tmpl_arg(
            st_tmpl_arg.clone(),
            st_arg.clone(),
        )),
    }
}

pub fn resolve_wildcard_values(
    params: &Params,
    pred: &CustomPredicate,
    args: &[Statement],
) -> Result<Vec<Value>> {
    // Check that all wildcard have consistent values as assigned in the statements while storing a
    // map of their values.
    // NOTE: We assume the statements have the same order as defined in the custom predicate.  For
    // disjunctions we expect Statement::None for the unused statements.
    let mut wildcard_map = vec![None; params.max_custom_predicate_wildcards];
    for (st_tmpl, st) in pred.statements.iter().zip(args) {
        let st_args = st.args();
        st_tmpl
            .args
            .iter()
            .zip(&st_args)
            .try_for_each(|(st_tmpl_arg, st_arg)| {
                check_st_tmpl(st_tmpl_arg, st_arg, &mut wildcard_map)
            })?;
    }

    // NOTE: We set unresolved wildcard slots with an empty value.  They can be unresolved because
    // they are beyond the number of used wildcards in this custom predicate, or they could be
    // private arguments that are unused in a particular disjunction.
    Ok(wildcard_map
        .into_iter()
        .map(|opt| opt.unwrap_or(Value::from(0)))
        .collect())
}

fn check_custom_pred(
    params: &Params,
    custom_pred_ref: &CustomPredicateRef,
    args: &[Statement],
    s_args: &[Value],
) -> Result<()> {
    let pred = custom_pred_ref.predicate();
    if pred.statements.len() != args.len() {
        return Err(Error::diff_amount(
            "custom predicate operation".to_string(),
            "statements".to_string(),
            pred.statements.len(),
            args.len(),
        ));
    }
    if pred.args_len != s_args.len() {
        return Err(Error::diff_amount(
            "custom predicate statement".to_string(),
            "args".to_string(),
            pred.args_len,
            s_args.len(),
        ));
    }

    // Count the number of statements that match the templates by predicate.
    let mut num_matches = 0;
    for (st_tmpl, st) in pred.statements.iter().zip(args) {
        let st_tmpl_pred = match &st_tmpl.pred {
            Predicate::BatchSelf(i) => Predicate::Custom(CustomPredicateRef {
                batch: custom_pred_ref.batch.clone(),
                index: *i,
            }),
            p => p.clone(),
        };
        if st_tmpl_pred == st.predicate() {
            num_matches += 1;
        }
    }

    let wildcard_map = resolve_wildcard_values(params, pred, args)?;

    // Check that the resolved wildcards match the statement arguments.
    for (arg_index, (s_arg, wc_value)) in s_args.iter().zip(wildcard_map.iter()).enumerate() {
        if *wc_value != *s_arg {
            return Err(Error::mismatched_wildcard_value_and_statement_arg(
                wc_value.clone(),
                s_arg.clone(),
                arg_index,
                pred.clone(),
            ));
        }
    }

    if pred.conjunction {
        if num_matches != pred.statements.len() {
            return Err(Error::unsatisfied_custom_predicate_conjunction(
                pred.clone(),
            ));
        }
    } else if num_matches == 0 {
        return Err(Error::unsatisfied_custom_predicate_disjunction(
            pred.clone(),
        ));
    }

    Ok(())
}

impl ToFields for Operation {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        todo!()
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "middleware::Operation:")?;
        writeln!(f, "  {:?} ", self.op_type())?;
        for arg in self.args().iter() {
            writeln!(f, "    {}", arg)?;
        }
        Ok(())
    }
}

/// Returns the value associated with `output_ref`.
/// If `output_ref` is a concrete value, returns that value.
/// Otherwise, `output_ref` was constructed using an `Equal` statement, and `input_st`
/// must be that statement.
pub(crate) fn value_from_op(input_st: &Statement, output_ref: &ValueRef) -> Option<Value> {
    match (input_st, output_ref) {
        (Statement::None, ValueRef::Literal(v)) => Some(v.clone()),
        (Statement::Equal(r1, ValueRef::Literal(v)), r2) if r1 == r2 => Some(v.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use num::BigUint;

    use crate::{
        backends::plonky2::primitives::{
            ec::{curve::GROUP_ORDER, schnorr::SecretKey},
            merkletree::MerkleTree,
        },
        middleware::{
            hash_value, AnchoredKey, Error, Key, Operation, Params, PodId, Result, Statement,
        },
    };

    #[test]
    fn check_container_ops() -> Result<()> {
        let params = Params::default();
        let pod_id = PodId::default();
        let root_ak = AnchoredKey::new(pod_id, Key::new("root".into()));
        let key_ak = AnchoredKey::new(pod_id, Key::new("key".into()));
        let val_ak = AnchoredKey::new(pod_id, Key::new("value".into()));

        // Form Merkle tree
        let kvs = (0..10)
            .map(|i| (hash_value(&i.into()).into(), i.into()))
            .collect::<HashMap<_, _>>();
        let mt = MerkleTree::new(params.max_depth_mt_containers, &kvs)?;
        let root_s = Statement::Equal(root_ak.clone().into(), mt.root().into());

        // Check existence proofs
        kvs.iter().try_for_each(|(k, v)| {
            // Form op args
            let key_s = Statement::Equal(key_ak.clone().into(), (*k).into());
            let value_s = Statement::Equal(val_ak.clone().into(), (*v).into());
            let (_, pf) = mt.prove(k)?;

            // Form op
            let op = Operation::ContainsFromEntries(root_s.clone(), key_s, value_s, pf);
            // Form output statement
            let st = Statement::Contains(
                root_ak.clone().into(),
                key_ak.clone().into(),
                val_ak.clone().into(),
            );

            // Check op against output statement
            op.check(&params, &st).and_then(|ind| {
                if ind {
                    Ok(())
                } else {
                    Err(Error::custom(format!(
                        "ContainedFromEntries check failed for pair ({},{})",
                        k, v
                    )))
                }
            })
        })?;

        // Check non-existence proofs similarly
        (50..60).try_for_each(|k| {
            let key_s = Statement::Equal(key_ak.clone().into(), k.into());
            let pf = mt.prove_nonexistence(&k.into())?;

            let op = Operation::NotContainsFromEntries(root_s.clone(), key_s, pf);
            let st = Statement::NotContains(root_ak.clone().into(), key_ak.clone().into());

            op.check(&params, &st).and_then(|ind| {
                if ind {
                    Ok(())
                } else {
                    Err(Error::custom(format!(
                        "NotContainedFromEntries check failed for key {}",
                        k
                    )))
                }
            })
        })
    }

    #[test]
    fn check_public_key_of_op() -> Result<()> {
        let fixed_sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let fixed_pk = fixed_sk.public_key();
        let rand_sk = SecretKey::new_rand();
        let rand_pk = rand_sk.public_key();
        let small_sk = SecretKey(BigUint::from(0x1u32));
        let small_pk = small_sk.public_key();
        let too_large_sk = SecretKey(small_sk.0.clone() + GROUP_ORDER.clone());
        assert_eq!(small_pk, too_large_sk.public_key());

        let test_cases = [
            // Valid pairs
            (fixed_pk, fixed_sk.clone(), true),
            (rand_pk, rand_sk.clone(), true),
            // Mismatched pairs
            (fixed_pk, rand_sk.clone(), false),
            (rand_pk, fixed_sk.clone(), false),
            // Above group order
            (small_pk, small_sk.clone(), true),
            (small_pk, too_large_sk.clone(), false),
        ];

        let params = Params::default();
        let pod_id = PodId::default();
        let pk_ak = AnchoredKey::new(pod_id, Key::new("pubkey".into()));
        let sk_ak = AnchoredKey::new(pod_id, Key::new("secret".into()));

        test_cases.iter().try_for_each(|(pk, sk, expect_good)| {
            // Form op args
            let pk_s = Statement::Equal(pk_ak.clone().into(), (*pk).into());
            let sk_s = Statement::Equal(sk_ak.clone().into(), sk.clone().into());

            // Form op
            let op = Operation::PublicKeyOf(pk_s.clone(), sk_s.clone());

            // Form output statement
            let st = Statement::PublicKeyOf(pk_ak.clone().into(), sk_ak.clone().into());

            // Check
            op.check(&params, &st).map(|is_good| {
                assert_eq!(
                    is_good, *expect_good,
                    "PublicKeyOf({}, {}) => {}",
                    pk, sk, is_good
                );
            })
        })
    }

    #[test]
    fn check_public_key_of_op_arg_types() -> Result<()> {
        let fixed_sk = SecretKey(BigUint::from(0x1234567890abcdefu64));
        let fixed_pk = fixed_sk.public_key();

        let params = Params::default();
        let pod_id = PodId::default();
        let pk_ak = AnchoredKey::new(pod_id, Key::new("pubkey".into()));
        let sk_ak = AnchoredKey::new(pod_id, Key::new("secret".into()));

        // Form op args
        let pk_s = Statement::Equal(pk_ak.clone().into(), fixed_pk.into());
        let sk_s = Statement::Equal(sk_ak.clone().into(), fixed_sk.clone().into());

        // Bad op and statement with bad first args
        let op = Operation::PublicKeyOf(pk_s.clone(), pk_s.clone());
        let st = Statement::PublicKeyOf(pk_ak.clone().into(), pk_ak.clone().into());

        // Check
        assert!(op.check(&params, &st).is_err());

        // Bad op and statement with bad second args
        let op = Operation::PublicKeyOf(sk_s.clone(), sk_s.clone());
        let st = Statement::PublicKeyOf(sk_ak.clone().into(), sk_ak.clone().into());

        // Check
        assert!(op.check(&params, &st).is_err());

        Ok(())
    }
}
