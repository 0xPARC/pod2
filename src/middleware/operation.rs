use std::collections::HashMap;

use anyhow::{anyhow, Result};

use super::{CustomPredicateRef, Statement};
use crate::{
    middleware::{AnchoredKey, CustomPredicate, PodId, Predicate, StatementTmpl, Value, SELF},
    util::hashmap_insert_no_dupe,
};

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
    pub fn code(&self) -> NativeOperation {
        use NativeOperation::*;
        match self {
            Self::None => None,
            Self::NewEntry => NewEntry,
            Self::CopyStatement(_) => CopyStatement,
            Self::EqualFromEntries(_, _) => EqualFromEntries,
            Self::NotEqualFromEntries(_, _) => NotEqualFromEntries,
            Self::GtFromEntries(_, _) => GtFromEntries,
            Self::LtFromEntries(_, _) => LtFromEntries,
            Self::TransitiveEqualFromStatements(_, _) => TransitiveEqualFromStatements,
            Self::GtToNotEqual(_) => GtToNotEqual,
            Self::LtToNotEqual(_) => LtToNotEqual,
            Self::ContainsFromEntries(_, _) => ContainsFromEntries,
            Self::NotContainsFromEntries(_, _) => NotContainsFromEntries,
            Self::RenameContainedBy(_, _) => RenameContainedBy,
            Self::SumOf(_, _, _) => SumOf,
            Self::ProductOf(_, _, _) => ProductOf,
            Self::MaxOf(_, _, _) => MaxOf,
            Self::Custom(_, _) => todo!(),
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
    pub fn op(op_code: NativeOperation, args: &[Statement]) -> Result<Self> {
        type NO = NativeOperation;
        let arg_tup = (
            args.get(0).cloned(),
            args.get(1).cloned(),
            args.get(2).cloned(),
        );
        Ok(match (op_code, arg_tup, args.len()) {
            (NO::None, (None, None, None), 0) => Self::None,
            (NO::NewEntry, (None, None, None), 0) => Self::NewEntry,
            (NO::CopyStatement, (Some(s), None, None), 1) => Self::CopyStatement(s),
            (NO::EqualFromEntries, (Some(s1), Some(s2), None), 2) => Self::EqualFromEntries(s1, s2),
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
        })
    }
    /// Checks the given operation against a statement.
    pub fn check(&self, output_statement: &Statement) -> Result<bool> {
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
            (
                Self::Custom(CustomPredicateRef(cpb, i), args),
                Custom(CustomPredicateRef(s_cpb, s_i), s_args),
            ) if cpb == s_cpb && i == s_i => {
                // Bind statement arguments
                let mut bindings = s_args
                    .into_iter()
                    .enumerate()
                    .flat_map(|(i, AnchoredKey(PodId(o), k))| {
                        vec![
                            (2 * i, Value::from(o.clone())),
                            (2 * i + 1, Value::from(k.clone())),
                        ]
                    })
                    .collect::<HashMap<_, _>>();

                // Single out custom predicate, replacing batch-self
                // references with custom predicate references.
                let custom_predicate = {
                    let cp = (**cpb).predicates[*i].clone();
                    CustomPredicate {
                        conjunction: cp.conjunction,
                        statements: cp
                            .statements
                            .into_iter()
                            .map(|StatementTmpl(p, args)| {
                                StatementTmpl(
                                    match p {
                                        Predicate::BatchSelf(i) => {
                                            Predicate::Custom(CustomPredicateRef(cpb.clone(), i))
                                        }
                                        _ => p,
                                    },
                                    args,
                                )
                            })
                            .collect(),
                        args_len: cp.args_len,
                    }
                };
                match custom_predicate.conjunction {
                    true if custom_predicate.statements.len() == args.len() => {
                        // Match op args against statement templates
                    let match_bindings = std::iter::zip(custom_predicate.statements, args).map(
                        |(s_tmpl, s)| s_tmpl.match_against(s)
                    ).collect::<Result<Vec<_>>>()
                        .map(|v| v.concat())?;
                    // Add bindings to binding table, throwing if there is an inconsistency.
                    match_bindings.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
                    Ok(true)
                    },
                    false if args.len() == 1 => {
                        // Match op arg against each statement template
                        custom_predicate.statements.into_iter().map(
                            |s_tmpl| {
                                let mut bindings = bindings.clone();
                                s_tmpl.match_against(&args[0])?.into_iter().try_for_each(|kv| hashmap_insert_no_dupe(&mut bindings, kv))?;
                                Ok::<_, anyhow::Error>(true)
                            }
                        ).find(|m| m.is_ok()).unwrap_or(Ok(false))
                    },
                    _ =>                     Err(anyhow!("Custom predicate statement template list {:?} does not match op argument list {:?}.", custom_predicate.statements, args))
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
