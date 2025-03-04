use std::collections::HashMap;
use std::fmt;

use anyhow::{anyhow, Result};

use super::{CustomPredicateRef, Statement};
use crate::{
    middleware::{
        AnchoredKey, CustomPredicate, Params, PodId, Predicate, StatementTmpl, Value, SELF,
    },
    util::hashmap_insert_no_dupe,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationType {
    Native(NativeOperation),
    Custom(CustomPredicateRef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeOperation {
    None = 0,
    NewEntry = 1,
    CopyStatement = 2,
    EqualFromEntries = 3,
    NotEqualFromEntries = 4,
    GtFromEntries = 5,
    LtFromEntries = 6,
    TransitiveEqualFromStatements = 7,
    GtToNotEqual = 8,
    LtToNotEqual = 9,
    ContainsFromEntries = 10,
    NotContainsFromEntries = 11,
    RenameContainedBy = 12,
    SumOf = 13,
    ProductOf = 14,
    MaxOf = 15,
}

// TODO: Refine this enum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation {
    None,
    NewEntry,
    CopyStatement(Statement),
    EqualFromEntries(Statement, Statement),
    NotEqualFromEntries(Statement, Statement),
    GtFromEntries(Statement, Statement),
    LtFromEntries(Statement, Statement),
    TransitiveEqualFromStatements(Statement, Statement),
    GtToNotEqual(Statement),
    LtToNotEqual(Statement),
    ContainsFromEntries(Statement, Statement),
    NotContainsFromEntries(Statement, Statement),
    RenameContainedBy(Statement, Statement),
    SumOf(Statement, Statement, Statement),
    ProductOf(Statement, Statement, Statement),
    MaxOf(Statement, Statement, Statement),
    Custom(CustomPredicateRef, Vec<Statement>),
}

impl Operation {
    pub fn code(&self) -> OperationType {
        type OT = OperationType;
        use NativeOperation::*;
        match self {
            Self::None => OT::Native(None),
            Self::NewEntry => OT::Native(NewEntry),
            Self::CopyStatement(_) => OT::Native(CopyStatement),
            Self::EqualFromEntries(_, _) => OT::Native(EqualFromEntries),
            Self::NotEqualFromEntries(_, _) => OT::Native(NotEqualFromEntries),
            Self::GtFromEntries(_, _) => OT::Native(GtFromEntries),
            Self::LtFromEntries(_, _) => OT::Native(LtFromEntries),
            Self::TransitiveEqualFromStatements(_, _) => OT::Native(TransitiveEqualFromStatements),
            Self::GtToNotEqual(_) => OT::Native(GtToNotEqual),
            Self::LtToNotEqual(_) => OT::Native(LtToNotEqual),
            Self::ContainsFromEntries(_, _) => OT::Native(ContainsFromEntries),
            Self::NotContainsFromEntries(_, _) => OT::Native(NotContainsFromEntries),
            Self::RenameContainedBy(_, _) => OT::Native(RenameContainedBy),
            Self::SumOf(_, _, _) => OT::Native(SumOf),
            Self::ProductOf(_, _, _) => OT::Native(ProductOf),
            Self::MaxOf(_, _, _) => OT::Native(MaxOf),
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
            Self::GtFromEntries(s1, s2) => vec![s1, s2],
            Self::LtFromEntries(s1, s2) => vec![s1, s2],
            Self::TransitiveEqualFromStatements(s1, s2) => vec![s1, s2],
            Self::GtToNotEqual(s) => vec![s],
            Self::LtToNotEqual(s) => vec![s],
            Self::ContainsFromEntries(s1, s2) => vec![s1, s2],
            Self::NotContainsFromEntries(s1, s2) => vec![s1, s2],
            Self::RenameContainedBy(s1, s2) => vec![s1, s2],
            Self::SumOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::ProductOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::MaxOf(s1, s2, s3) => vec![s1, s2, s3],
            Self::Custom(_, args) => args,
        }
    }
    /// Forms operation from op-code and arguments.
    pub fn op(op_code: OperationType, args: &[Statement]) -> Result<Self> {
        type NO = NativeOperation;
        let arg_tup = (
            args.get(0).cloned(),
            args.get(1).cloned(),
            args.get(2).cloned(),
        );
        Ok(match op_code {
            OperationType::Native(o) => match (o, arg_tup, args.len()) {
                (NO::None, (None, None, None), 0) => Self::None,
                (NO::NewEntry, (None, None, None), 0) => Self::NewEntry,
                (NO::CopyStatement, (Some(s), None, None), 1) => Self::CopyStatement(s),
                (NO::EqualFromEntries, (Some(s1), Some(s2), None), 2) => {
                    Self::EqualFromEntries(s1, s2)
                }
                (NO::NotEqualFromEntries, (Some(s1), Some(s2), None), 2) => {
                    Self::NotEqualFromEntries(s1, s2)
                }
                (NO::GtFromEntries, (Some(s1), Some(s2), None), 2) => Self::GtFromEntries(s1, s2),
                (NO::LtFromEntries, (Some(s1), Some(s2), None), 2) => Self::LtFromEntries(s1, s2),
                (NO::ContainsFromEntries, (Some(s1), Some(s2), None), 2) => {
                    Self::ContainsFromEntries(s1, s2)
                }
                (NO::NotContainsFromEntries, (Some(s1), Some(s2), None), 2) => {
                    Self::NotContainsFromEntries(s1, s2)
                }
                (NO::RenameContainedBy, (Some(s1), Some(s2), None), 2) => {
                    Self::RenameContainedBy(s1, s2)
                }
                (NO::SumOf, (Some(s1), Some(s2), Some(s3)), 3) => Self::SumOf(s1, s2, s3),
                (NO::ProductOf, (Some(s1), Some(s2), Some(s3)), 3) => Self::ProductOf(s1, s2, s3),
                (NO::MaxOf, (Some(s1), Some(s2), Some(s3)), 3) => Self::MaxOf(s1, s2, s3),
                _ => Err(anyhow!(
                    "Ill-formed operation {:?} with arguments {:?}.",
                    op_code,
                    args
                ))?,
            },
            OperationType::Custom(cpr) => Self::Custom(cpr, args.to_vec()),
        })
    }
    /// Checks the given operation against a statement.
    pub fn check(&self, params: &Params, output_statement: &Statement) -> Result<bool> {
        use Statement::*;
        match (self, output_statement) {
            (Self::None, None) => Ok(true),
            (Self::NewEntry, ValueOf(AnchoredKey(pod_id, _), _)) => Ok(pod_id == &SELF),
            (Self::CopyStatement(s1), s2) => Ok(s1 == s2),
            (Self::EqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), Equal(ak3, ak4)) => {
                Ok(v1 == v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::NotEqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), NotEqual(ak3, ak4)) => {
                Ok(v1 != v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::GtFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), Gt(ak3, ak4)) => {
                Ok(v1 > v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::LtFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)), Lt(ak3, ak4)) => {
                Ok(v1 < v2 && ak3 == ak1 && ak4 == ak2)
            }
            (Self::ContainsFromEntries(_, _), Contains(_, _)) =>
            /* TODO */
            {
                Ok(true)
            }
            (Self::NotContainsFromEntries(_, _), NotContains(_, _)) =>
            /* TODO */
            {
                Ok(true)
            }
            (
                Self::TransitiveEqualFromStatements(Equal(ak1, ak2), Equal(ak3, ak4)),
                Equal(ak5, ak6),
            ) => Ok(ak2 == ak3 && ak5 == ak1 && ak6 == ak4),
            (Self::GtToNotEqual(Gt(ak1, ak2)), NotEqual(ak3, ak4)) => Ok(ak1 == ak3 && ak2 == ak4),
            (Self::LtToNotEqual(Lt(ak1, ak2)), NotEqual(ak3, ak4)) => Ok(ak1 == ak3 && ak2 == ak4),
            (Self::RenameContainedBy(Contains(ak1, ak2), Equal(ak3, ak4)), Contains(ak5, ak6)) => {
                Ok(ak1 == ak3 && ak4 == ak5 && ak2 == ak6)
            }
            (
                Self::SumOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3)),
                SumOf(ak4, ak5, ak6),
            ) => {
                let v1: i64 = v1.clone().try_into()?;
                let v2: i64 = v2.clone().try_into()?;
                let v3: i64 = v3.clone().try_into()?;
                Ok((v1 == v2 + v3) && ak4 == ak1 && ak5 == ak2 && ak6 == ak3)
            }
            (Self::Custom(CustomPredicateRef(cpb, i), args), Custom(cpr, s_args))
                if cpb == &cpr.0 && i == &cpr.1 =>
            {
                // Bind according to custom predicate pattern match against arg list.
                let bindings = cpr.match_against(args)?;
                // Check arg length
                let arg_len = cpr.arg_len();
                if arg_len != 2 * s_args.len() {
                    Err(anyhow!("Custom predicate arg list {:?} must have {} arguments after destructuring.", s_args, arg_len))
                } else {
                    let bound_args = (0..arg_len)
                        .map(|i| {
                            bindings.get(&i).cloned().ok_or(anyhow!(
                                "Wildcard {} of custom predicate {:?} is unbound.",
                                i,
                                cpr
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let s_args = s_args
                        .into_iter()
                        .flat_map(|AnchoredKey(o, k)| [Value::from(o.0.clone()), k.clone().into()])
                        .collect::<Vec<_>>();
                    if bound_args != s_args {
                        Err(anyhow!("Arguments to output statement {} do not match those implied by operation {:?}", output_statement,self))
                    } else {
                        Ok(true)
                    }
                }
            }
            _ => Err(anyhow!(
                "Invalid deduction: {:?} ⇏ {:#}",
                self,
                output_statement
            )),
        }
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "middleware::Operation:")?;
        writeln!(f, "  {:?} ", self.code())?;
        for (i, arg) in self.args().iter().enumerate() {
            writeln!(f, "    {}", arg)?;
        }
        Ok(())
    }
}
