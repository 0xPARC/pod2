use std::{fmt, iter};

use log::error;
use plonky2::field::types::Field;
use serde::{Deserialize, Serialize};

use crate::{
    backends::plonky2::primitives::merkletree::MerkleProof,
    middleware::{
        custom::KeyOrWildcard, AnchoredKey, CustomPredicate, CustomPredicateRef, Error,
        NativePredicate, Params, Predicate, Result, Statement, StatementArg, StatementTmplArg,
        ToFields, Wildcard, WildcardValue, F, SELF,
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
                NativeOperation::NewEntry => Some(Predicate::Native(NativePredicate::ValueOf)),
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
        let arg_tup = (
            args.first().cloned(),
            args.get(1).cloned(),
            args.get(2).cloned(),
        );
        Ok(match op_code {
            OperationType::Native(o) => match (o, arg_tup, aux.clone(), args.len()) {
                (NO::None, (None, None, None), OA::None, 0) => Self::None,
                (NO::NewEntry, (None, None, None), OA::None, 0) => Self::NewEntry,
                (NO::CopyStatement, (Some(s), None, None), OA::None, 1) => Self::CopyStatement(s),
                (NO::EqualFromEntries, (Some(s1), Some(s2), None), OA::None, 2) => {
                    Self::EqualFromEntries(s1, s2)
                }
                (NO::NotEqualFromEntries, (Some(s1), Some(s2), None), OA::None, 2) => {
                    Self::NotEqualFromEntries(s1, s2)
                }
                (NO::LtEqFromEntries, (Some(s1), Some(s2), None), OA::None, 2) => {
                    Self::LtEqFromEntries(s1, s2)
                }
                (NO::LtFromEntries, (Some(s1), Some(s2), None), OA::None, 2) => {
                    Self::LtFromEntries(s1, s2)
                }
                (
                    NO::ContainsFromEntries,
                    (Some(s1), Some(s2), Some(s3)),
                    OA::MerkleProof(pf),
                    3,
                ) => Self::ContainsFromEntries(s1, s2, s3, pf),
                (
                    NO::NotContainsFromEntries,
                    (Some(s1), Some(s2), None),
                    OA::MerkleProof(pf),
                    2,
                ) => Self::NotContainsFromEntries(s1, s2, pf),
                (NO::SumOf, (Some(s1), Some(s2), Some(s3)), OA::None, 3) => Self::SumOf(s1, s2, s3),
                (NO::ProductOf, (Some(s1), Some(s2), Some(s3)), OA::None, 3) => {
                    Self::ProductOf(s1, s2, s3)
                }
                (NO::MaxOf, (Some(s1), Some(s2), Some(s3)), OA::None, 3) => Self::MaxOf(s1, s2, s3),
                (NO::HashOf, (Some(s1), Some(s2), Some(s3)), OA::None, 3) => {
                    Self::HashOf(s1, s2, s3)
                }
                _ => Err(Error::custom(format!(
                    "Ill-formed operation {:?} with arguments {:?}.",
                    op_code, args
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
    /// Checks the given operation against a statement.
    pub fn check(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        use Statement::*;
        match (self, output_statement) {
            (Self::None, None) => Ok(true),
            (Self::NewEntry, ValueOf(AnchoredKey { pod_id, .. }, _)) => Ok(pod_id == &SELF),
            (Self::CopyStatement(s1), s2) => Ok(s1 == s2),
            (Self::EqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), Equal(ak3, ak4)) => {
                Ok(v1 == v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::NotEqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), NotEqual(ak3, ak4)) => {
                Ok(v1 != v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::LtEqFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), LtEq(ak3, ak4)) => {
                Ok(v1 <= v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::LtFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), Lt(ak3, ak4)) => {
                Ok(v1 < v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::ContainsFromEntries(_, _, _, _), Contains(_, _, _)) =>
            /* TODO */
            {
                Ok(true)
            }
            (Self::NotContainsFromEntries(_, _, _), NotContains(_, _)) =>
            /* TODO */
            {
                Ok(true)
            }
            (
                Self::TransitiveEqualFromStatements(Equal(ak1, ak2), Equal(ak3, ak4)),
                Equal(ak5, ak6),
            ) => Ok(ak2 == ak3 && ak5 == ak1 && ak6 == ak4),
            (Self::LtToNotEqual(Lt(ak1, ak2)), NotEqual(ak3, ak4)) => Ok(ak1 == ak3 && ak2 == ak4),
            (
                Self::SumOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3)),
                SumOf(ak4, ak5, ak6),
            ) => {
                let v1: i64 = v1.typed().try_into()?;
                let v2: i64 = v2.typed().try_into()?;
                let v3: i64 = v3.typed().try_into()?;
                Ok((v1 == v2 + v3) && ak4 == ak1 && ak5 == ak2 && ak6 == ak3)
            }
            (Self::Custom(CustomPredicateRef { batch, index }, args), Custom(cpr, s_args))
                if batch == &cpr.batch && index == &cpr.index =>
            {
                check_custom_pred(params, cpr, args, s_args)
            }
            _ => Err(Error::invalid_deduction(
                self.clone(),
                output_statement.clone(),
            )),
        }
    }
}

/// Check that a StatementArg follows a StatementTmplArg based on the currently mapped wildcards.
/// Update the wildcard map with newly found wildcards.
pub fn check_st_tmpl(
    st_tmpl_arg: &StatementTmplArg,
    st_arg: &StatementArg,
    // Map from wildcards to values that we have seen so far.
    wildcard_map: &mut [Option<WildcardValue>],
) -> bool {
    // Check that the value `v` at wildcard `wc` exists in the map or set it.
    fn check_or_set(
        v: WildcardValue,
        wc: &Wildcard,
        wildcard_map: &mut [Option<WildcardValue>],
    ) -> bool {
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
            StatementTmplArg::AnchoredKey(pod_id_wc, key_or_wc),
            StatementArg::Key(AnchoredKey { pod_id, key }),
        ) => {
            let pod_id_ok = check_or_set(WildcardValue::PodId(*pod_id), pod_id_wc, wildcard_map);
            let key_ok = match key_or_wc {
                KeyOrWildcard::Key(tmpl_key) => tmpl_key == key,
                KeyOrWildcard::Wildcard(key_wc) => {
                    check_or_set(WildcardValue::Key(key.clone()), key_wc, wildcard_map)
                }
            };
            pod_id_ok && key_ok
        }
        (StatementTmplArg::WildcardLiteral(wc), StatementArg::WildcardLiteral(v)) => {
            check_or_set(v.clone(), wc, wildcard_map)
        }
        _ => false,
    }
}

pub fn resolve_wildcard_values(
    params: &Params,
    pred: &CustomPredicate,
    args: &[Statement],
) -> Option<Vec<WildcardValue>> {
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
            .map(|opt| opt.unwrap_or(WildcardValue::None))
            .collect(),
    )
}

fn check_custom_pred(
    params: &Params,
    custom_pred_ref: &CustomPredicateRef,
    args: &[Statement],
    s_args: &[WildcardValue],
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
