use std::{fmt, iter};

use log::error;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::primitives::merkletree::MerkleProof,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
            (Self::ContainsFromEntries(_, _, _, _), Contains(_, _, _)) =>
            /* TODO */
            {
                true
            }
            (Self::NotContainsFromEntries(_, _, _), NotContains(_, _)) =>
            /* TODO */
            {
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
            (Self::MaxOf(s1, s2, s3), ProductOf(v4, v5, v6)) => {
                Self::check_int_fn(&val(v4, s1)?, &val(v5, s2)?, &val(v6, s3)?, max_op)?
            }
            (Self::HashOf(s1, s2, s3), ProductOf(v4, v5, v6)) => {
                val(v4, s1)? == hash_op(val(v5, s2)?, val(v6, s3)?)
            }
            (Self::Custom(CustomPredicateRef { batch, index }, args), Custom(cpr, s_args))
                if batch == &cpr.batch && index == &cpr.index =>
            {
                check_custom_pred(params, cpr, args, s_args)?
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
) -> bool {
    // Check that the value `v` at wildcard `wc` exists in the map or set it.
    fn check_or_set(v: Value, wc: &Wildcard, wildcard_map: &mut [Option<Value>]) -> bool {
        if let Some(prev) = &wildcard_map[wc.index] {
            if *prev != v {
                // TODO: Return nice error
                return false;
            }
        } else {
            wildcard_map[wc.index] = Some(v);
        }
        true
    }

    match (st_tmpl_arg, st_arg) {
        (StatementTmplArg::None, StatementArg::None) => true,
        (StatementTmplArg::Literal(lhs), StatementArg::Literal(rhs)) if lhs == rhs => true,
        (
            StatementTmplArg::AnchoredKey(pod_id_wc, key_tmpl),
            StatementArg::Key(AnchoredKey { pod_id, key }),
        ) => {
            let pod_id_ok = check_or_set(Value::from(*pod_id), pod_id_wc, wildcard_map);
            pod_id_ok && (key_tmpl == key)
        }
        (StatementTmplArg::WildcardLiteral(wc), StatementArg::Literal(v)) => {
            check_or_set(v.clone(), wc, wildcard_map)
        }
        _ => {
            println!("DBG {:?} {:?}", st_tmpl_arg, st_arg);
            false
        }
    }
}

pub fn resolve_wildcard_values(
    params: &Params,
    pred: &CustomPredicate,
    args: &[Statement],
) -> Option<Vec<Value>> {
    // Check that all wildcard have consistent values as assigned in the statements while storing a
    // map of their values.
    // NOTE: We assume the statements have the same order as defined in the custom predicate.  For
    // disjunctions we expect Statement::None for the unused statements.
    let mut wildcard_map = vec![None; params.max_custom_predicate_wildcards];
    for (st_tmpl, st) in pred.statements.iter().zip(args) {
        let st_args = st.args();
        for (st_tmpl_arg, st_arg) in st_tmpl.args.iter().zip(&st_args) {
            if !check_st_tmpl(st_tmpl_arg, st_arg, &mut wildcard_map) {
                // TODO: Better errors.  Example:
                // println!("{} doesn't match {}", st_arg, st_tmpl_arg);
                // println!("{} doesn't match {}", st, st_tmpl);
                return None;
            }
        }
    }

    // NOTE: We set unresolved wildcard slots with an empty value.  They can be unresolved because
    // they are beyond the number of used wildcards in this custom predicate, or they could be
    // private arguments that are unused in a particular disjunction.
    Some(
        wildcard_map
            .into_iter()
            .map(|opt| opt.unwrap_or(Value::from(0)))
            .collect(),
    )
}

fn check_custom_pred(
    params: &Params,
    custom_pred_ref: &CustomPredicateRef,
    args: &[Statement],
    s_args: &[Value],
) -> Result<bool> {
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

    let wildcard_map = match resolve_wildcard_values(params, pred, args) {
        Some(wc_map) => wc_map,
        None => return Ok(false),
    };

    // Check that the resolved wildcard match the statement arguments.
    for (s_arg, wc_value) in s_args.iter().zip(wildcard_map.iter()) {
        if *wc_value != *s_arg {
            return Ok(false);
        }
    }

    if pred.conjunction {
        Ok(num_matches == pred.statements.len())
    } else {
        Ok(num_matches > 0)
    }
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
