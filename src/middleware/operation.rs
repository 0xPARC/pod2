use std::fmt;

use anyhow::{anyhow, Result};

use super::{CustomPredicateRef, NativePredicate, Statement, StatementArg};
use crate::{
    constants::MAX_DEPTH,
    middleware::{
        hash_fields, keypath, kv_hash, AnchoredKey, Hash, Params, Predicate, Value, EMPTY, SELF,
        VALUE_SIZE,
    },
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
    BranchesFromEntries = 12,
    LeafFromEntries = 13,
    GoesLeft = 14,
    GoesRight = 15,
    IsNullTree = 16,
    SumOf = 17,
    ProductOf = 18,
    MaxOf = 19,
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
                NativeOperation::GtFromEntries => Some(Predicate::Native(NativePredicate::Gt)),
                NativeOperation::LtFromEntries => Some(Predicate::Native(NativePredicate::Lt)),
                NativeOperation::TransitiveEqualFromStatements => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::GtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::LtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::ContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::Contains))
                }
                NativeOperation::NotContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::NotContains))
                }
                NativeOperation::BranchesFromEntries => {
                    Some(Predicate::Native(NativePredicate::Branches))
                }
                NativeOperation::LeafFromEntries => Some(Predicate::Native(NativePredicate::Leaf)),

                NativeOperation::IsNullTree => Some(Predicate::Native(NativePredicate::IsNullTree)),
                NativeOperation::GoesLeft => Some(Predicate::Native(NativePredicate::GoesLeft)),
                NativeOperation::GoesRight => Some(Predicate::Native(NativePredicate::GoesRight)),

                NativeOperation::SumOf => Some(Predicate::Native(NativePredicate::SumOf)),
                NativeOperation::ProductOf => Some(Predicate::Native(NativePredicate::ProductOf)),
                NativeOperation::MaxOf => Some(Predicate::Native(NativePredicate::MaxOf)),
            },
            OperationType::Custom(cpr) => Some(Predicate::Custom(cpr.clone())),
        }
    }
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
    BranchesFromEntries(Statement, Statement, Statement),
    LeafFromEntries(Statement, Statement, Statement),
    IsNullTree(Statement),
    GoesLeft(Statement, Statement),
    GoesRight(Statement, Statement),
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
            Self::BranchesFromEntries(_, _, _) => OT::Native(BranchesFromEntries),
            Self::LeafFromEntries(_, _, _) => OT::Native(LeafFromEntries),
            Self::IsNullTree(_) => OT::Native(IsNullTree),
            Self::GoesLeft(_, _) => OT::Native(GoesLeft),
            Self::GoesRight(_, _) => OT::Native(GoesRight),
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
            Self::BranchesFromEntries(s1, s2, s3) => vec![s1, s2, s3],
            Self::LeafFromEntries(s1, s2, s3) => vec![s1, s2, s3],
            Self::IsNullTree(s) => vec![s],
            Self::GoesLeft(s1, s2) => vec![s1, s2],
            Self::GoesRight(s1, s2) => vec![s1, s2],
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
            args.first().cloned(),
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
                (NO::BranchesFromEntries, (Some(s1), Some(s2), Some(s3)), 3) => {
                    Self::BranchesFromEntries(s1, s2, s3)
                }
                (NO::LeafFromEntries, (Some(s1), Some(s2), Some(s3)), 3) => {
                    Self::LeafFromEntries(s1, s2, s3)
                }
                (NO::IsNullTree, (Some(s), None, None), 1) => Self::IsNullTree(s),
                (NO::GoesLeft, (Some(s1), Some(s2), None), 2) => Self::GoesLeft(s1, s2),
                (NO::GoesRight, (Some(s1), Some(s2), None), 2) => Self::GoesRight(s1, s2),
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
    /// Gives the output statement of the given operation, where determined
    /// A ValueOf statement is not determined by the NewEntry operation, so returns Ok(None)
    /// The outer Result is error handling
    pub fn output_statement(&self) -> Result<Option<Statement>> {
        use Statement::*;
        let pred: Option<Predicate> = self.code().output_predicate();

        let st_args: Option<Vec<StatementArg>> = match self {
            Self::None => Some(vec![]),
            Self::NewEntry => Option::None,
            Self::CopyStatement(s1) => Some(s1.args()),
            Self::EqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) if v1 == v2 => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::NotEqualFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) if v1 != v2 => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::GtFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) if v1 > v2 => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::LtFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) if v1 < v2 => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::TransitiveEqualFromStatements(Equal(ak1, ak2), Equal(ak3, ak4)) if ak2 == ak3 => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak4)])
            }
            Self::GtToNotEqual(Gt(ak1, ak2)) => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::LtToNotEqual(Gt(ak1, ak2)) => {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::ContainsFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) =>
            /* TODO */
            {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::NotContainsFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2)) =>
            /* TODO */
            {
                Some(vec![StatementArg::Key(*ak1), StatementArg::Key(*ak2)])
            }
            Self::BranchesFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3))
                if Hash::from(*v1) == hash_fields(&[v2.0, v3.0].concat()) =>
            {
                Some(vec![
                    StatementArg::Key(*ak1),
                    StatementArg::Key(*ak2),
                    StatementArg::Key(*ak3),
                ])
            }
            Self::LeafFromEntries(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3))
                if Hash::from(*v1) == kv_hash(v2, Some(*v3)) =>
            {
                Some(vec![
                    StatementArg::Key(*ak1),
                    StatementArg::Key(*ak2),
                    StatementArg::Key(*ak3),
                ])
            }
            Self::IsNullTree(ValueOf(ak, v)) if v == &EMPTY => Some(vec![StatementArg::Key(*ak)]),
            Self::GoesLeft(ValueOf(ak, key), ValueOf(_, depth))
                if ({
                    let depth_index = <Value as TryInto<i64>>::try_into(*depth)? as usize;
                    let key_bits = keypath(MAX_DEPTH, *key)?;
                    !key_bits[depth_index]
                }) =>
            {
                Some(vec![StatementArg::Key(*ak), StatementArg::Literal(*depth)])
            }
            Self::GoesRight(ValueOf(ak, key), ValueOf(_, depth))
                if {
                    let depth_index = <Value as TryInto<i64>>::try_into(*depth)? as usize;
                    let key_bits = keypath(MAX_DEPTH, *key)?;
                    key_bits[depth_index]
                } =>
            {
                Some(vec![StatementArg::Key(*ak), StatementArg::Literal(*depth)])
            }
            Self::SumOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3))
                if {
                    let v1: i64 = (*v1).try_into()?;
                    let v2: i64 = (*v2).try_into()?;
                    let v3: i64 = (*v3).try_into()?;
                    v1 == v2 + v3
                } =>
            {
                Some(vec![
                    StatementArg::Key(*ak1),
                    StatementArg::Key(*ak2),
                    StatementArg::Key(*ak3),
                ])
            }
            Self::ProductOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3))
                if ({
                    let v1: i64 = (*v1).try_into()?;
                    let v2: i64 = (*v2).try_into()?;
                    let v3: i64 = (*v3).try_into()?;
                    v1 == v2 * v3
                }) =>
            {
                Some(vec![
                    StatementArg::Key(*ak1),
                    StatementArg::Key(*ak2),
                    StatementArg::Key(*ak3),
                ])
            }
            Self::MaxOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3))
                if ({
                    let v1: i64 = (*v1).try_into()?;
                    let v2: i64 = (*v2).try_into()?;
                    let v3: i64 = (*v3).try_into()?;
                    v1 == std::cmp::max(v2, v3)
                }) =>
            {
                Some(vec![
                    StatementArg::Key(*ak1),
                    StatementArg::Key(*ak2),
                    StatementArg::Key(*ak3),
                ])
            }
            Self::Custom(_, _) => todo!(),
            _ => return Err(anyhow!("Invalid operation: {}", self)),
        };

        let x: Option<Result<Statement>> = pred
            .zip(st_args)
            .map(|(pred, st_args)| Statement::from_args(pred, st_args));
        x.transpose()
    }
    /// Checks the given operation against a statement.
    pub fn check(&self, _params: &Params, output_statement: &Statement) -> Result<bool> {
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
            (
                Self::SumOf(ValueOf(ak1, v1), ValueOf(ak2, v2), ValueOf(ak3, v3)),
                SumOf(ak4, ak5, ak6),
            ) => {
                let v1: i64 = (*v1).try_into()?;
                let v2: i64 = (*v2).try_into()?;
                let v3: i64 = (*v3).try_into()?;
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
                        .iter()
                        .flat_map(|AnchoredKey(o, k)| [Value::from(o.0), (*k).into()])
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
        for arg in self.args().iter() {
            writeln!(f, "    {}", arg)?;
        }
        Ok(())
    }
}
