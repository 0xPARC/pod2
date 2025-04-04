use std::fmt;

use serde::{Deserialize, Serialize};

use super::{CustomPredicateRef, NativePredicate, Predicate, SignedPod, Statement, Value};
use crate::middleware::{self, OperationAux};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationArg {
    Statement(Statement),
    Literal(Value),
    Entry(String, Value),
}

impl fmt::Display for OperationArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationArg::Statement(s) => write!(f, "{}", s),
            OperationArg::Literal(v) => write!(f, "{}", v),
            OperationArg::Entry(k, v) => write!(f, "({}, {})", k, v),
        }
    }
}

impl From<Value> for OperationArg {
    fn from(v: Value) -> Self {
        Self::Literal(v)
    }
}

impl From<&Value> for OperationArg {
    fn from(v: &Value) -> Self {
        Self::Literal(v.clone())
    }
}

impl From<&str> for OperationArg {
    fn from(s: &str) -> Self {
        Self::Literal(Value::from(s))
    }
}

impl From<i64> for OperationArg {
    fn from(v: i64) -> Self {
        Self::Literal(Value::from(v))
    }
}

impl From<bool> for OperationArg {
    fn from(b: bool) -> Self {
        Self::Literal(Value::from(b))
    }
}

impl From<(&SignedPod, &str)> for OperationArg {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        Self::Statement((pod, key).into())
    }
}

impl From<Statement> for OperationArg {
    fn from(s: Statement) -> Self {
        Self::Statement(s)
    }
}

impl<V: Into<Value>> From<(&str, V)> for OperationArg {
    fn from((key, value): (&str, V)) -> Self {
        Self::Entry(key.to_string(), value.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationType {
    Native(NativeOperation),
    Custom(CustomPredicateRef),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
    SumOf = 13,
    ProductOf = 14,
    MaxOf = 15,
    DictContainsFromEntries = 16,
    DictNotContainsFromEntries = 17,
    SetContainsFromEntries = 18,
    SetNotContainsFromEntries = 19,
    ArrayContainsFromEntries = 20,
}

impl TryFrom<OperationType> for middleware::OperationType {
    type Error = anyhow::Error;
    fn try_from(fe_ot: OperationType) -> Result<Self, Self::Error> {
        type FeOT = OperationType;
        type FeNO = NativeOperation;
        type MwOT = middleware::OperationType;
        type MwNO = middleware::NativeOperation;
        let mw_ot = match fe_ot {
            FeOT::Native(FeNO::None) => MwOT::Native(MwNO::None),
            FeOT::Native(FeNO::NewEntry) => MwOT::Native(MwNO::NewEntry),
            FeOT::Native(FeNO::CopyStatement) => MwOT::Native(MwNO::CopyStatement),
            FeOT::Native(FeNO::EqualFromEntries) => MwOT::Native(MwNO::EqualFromEntries),
            FeOT::Native(FeNO::NotEqualFromEntries) => MwOT::Native(MwNO::NotEqualFromEntries),
            FeOT::Native(FeNO::GtFromEntries) => MwOT::Native(MwNO::GtFromEntries),
            FeOT::Native(FeNO::LtFromEntries) => MwOT::Native(MwNO::LtFromEntries),
            FeOT::Native(FeNO::TransitiveEqualFromStatements) => {
                MwOT::Native(MwNO::TransitiveEqualFromStatements)
            }
            FeOT::Native(FeNO::GtToNotEqual) => MwOT::Native(MwNO::GtToNotEqual),
            FeOT::Native(FeNO::LtToNotEqual) => MwOT::Native(MwNO::LtToNotEqual),
            FeOT::Native(FeNO::SumOf) => MwOT::Native(MwNO::SumOf),
            FeOT::Native(FeNO::ProductOf) => MwOT::Native(MwNO::ProductOf),
            FeOT::Native(FeNO::MaxOf) => MwOT::Native(MwNO::MaxOf),
            FeOT::Native(FeNO::DictContainsFromEntries) => MwOT::Native(MwNO::ContainsFromEntries),
            FeOT::Native(FeNO::DictNotContainsFromEntries) => {
                MwOT::Native(MwNO::NotContainsFromEntries)
            }
            FeOT::Native(FeNO::SetContainsFromEntries) => MwOT::Native(MwNO::ContainsFromEntries),
            FeOT::Native(FeNO::SetNotContainsFromEntries) => {
                MwOT::Native(MwNO::NotContainsFromEntries)
            }
            FeOT::Native(FeNO::ArrayContainsFromEntries) => MwOT::Native(MwNO::ContainsFromEntries),
            FeOT::Custom(mw_cpr) => MwOT::Custom(mw_cpr.into()),
        };
        Ok(mw_ot)
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
                NativeOperation::GtFromEntries => Some(Predicate::Native(NativePredicate::Gt)),
                NativeOperation::LtFromEntries => Some(Predicate::Native(NativePredicate::Lt)),
                NativeOperation::TransitiveEqualFromStatements => {
                    Some(Predicate::Native(NativePredicate::Equal))
                }
                NativeOperation::GtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::LtToNotEqual => Some(Predicate::Native(NativePredicate::NotEqual)),
                NativeOperation::SumOf => Some(Predicate::Native(NativePredicate::SumOf)),
                NativeOperation::ProductOf => Some(Predicate::Native(NativePredicate::ProductOf)),
                NativeOperation::MaxOf => Some(Predicate::Native(NativePredicate::MaxOf)),
                NativeOperation::DictContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::DictContains))
                }
                NativeOperation::DictNotContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::DictNotContains))
                }
                NativeOperation::SetContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::SetContains))
                }
                NativeOperation::SetNotContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::SetNotContains))
                }
                NativeOperation::ArrayContainsFromEntries => {
                    Some(Predicate::Native(NativePredicate::ArrayContains))
                }
            },
            OperationType::Custom(cpr) => Some(Predicate::Custom(cpr.clone())),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operation(pub OperationType, pub Vec<OperationArg>, pub OperationAux);

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}
