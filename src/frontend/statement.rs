use super::{AnchoredKey, NativePredicate, Predicate, SignedPod, Value};
use crate::middleware;
use anyhow::{anyhow, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub enum StatementArg {
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(r) => write!(f, "{}.{}", r.origin.pod_id, r.key),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct Statement {
    pub predicate: Predicate,
    pub args: Vec<StatementArg>,
}

impl Statement {
    pub fn new(predicate: Predicate, args: Vec<StatementArg>) -> Self {
        Self { predicate, args }
    }
}

impl From<(&SignedPod, &str)> for Statement {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        // TODO: TryFrom.
        let value = pod
            .kvs
            .get(key)
            .cloned()
            .unwrap_or_else(|| panic!("Key {} is not present in POD: {}", key, pod));
        Statement {
            predicate: Predicate::Native(NativePredicate::ValueOf),
            args: vec![
                StatementArg::Key(AnchoredKey::new(pod.origin(), key.to_string())),
                StatementArg::Literal(value),
            ],
        }
    }
}

#[derive(Debug)]
pub struct ManualConversionRequired();

impl std::fmt::Display for StatementConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Statement conversion error: statement conversion must be implemented manually."
        )
    }
}

impl std::error::Error for StatementConversionError {}

#[derive(Debug)]
pub enum StatementConversionError {
    MCR(ManualConversionRequired),
    Error(anyhow::Error),
}

impl From<anyhow::Error> for StatementConversionError {
    fn from(value: anyhow::Error) -> Self {
        Self::Error(value)
    }
}

impl TryFrom<Statement> for middleware::Statement {
    type Error = StatementConversionError;
    fn try_from(s: Statement) -> Result<Self, StatementConversionError> {
        type MS = middleware::Statement;
        type NP = NativePredicate;
        type SA = StatementArg;
        let args = (
            s.args.first().cloned(),
            s.args.get(1).cloned(),
            s.args.get(2).cloned(),
        );
        Ok(match &s.predicate {
            Predicate::Native(np) => match (np, args) {
                (NP::None, (None, None, None)) => MS::None,
                (NP::ValueOf, (Some(SA::Key(ak)), Some(StatementArg::Literal(v)), None)) => {
                    MS::ValueOf(ak.into(), (&v).into())
                }
                (NP::Equal, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Equal(ak1.into(), ak2.into())
                }
                (NP::NotEqual, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotEqual(ak1.into(), ak2.into())
                }
                (NP::Gt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Gt(ak1.into(), ak2.into())
                }
                (NP::Lt, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Lt(ak1.into(), ak2.into())
                }
                (NP::SumOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::SumOf(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::ProductOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::ProductOf(ak1.into(), ak2.into(), ak3.into())
                }
                (NP::MaxOf, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3)))) => {
                    MS::MaxOf(ak1.into(), ak2.into(), ak3.into())
                }
                (
                    NP::DictContains,
                    (Some(SA::Key(ak1)), Some(SA::Key(ak2)), Some(SA::Key(ak3))),
                ) => MS::Contains(ak1.into(), ak2.into(), ak3.into()),
                (NP::DictNotContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotContains(ak1.into(), ak2.into())
                }
                (NP::SetContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    return Err(StatementConversionError::MCR(ManualConversionRequired()));
                }
                (NP::SetNotContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotContains(ak1.into(), ak2.into())
                }
                _ => Err(anyhow!("Ill-formed statement: {}", s))?,
            },
            Predicate::Custom(cpr) => MS::Custom(
                cpr.clone(),
                s.args
                    .iter()
                    .map(|arg| match arg {
                        StatementArg::Key(ak) => Ok(ak.clone().into()),
                        _ => Err(anyhow!("Invalid statement arg: {}", arg)),
                    })
                    .collect::<Result<Vec<_>>>()?,
            ),
            _ => Err(anyhow!("Ill-formed statement: {}", s))?,
        })
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} ", self.predicate)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i != 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}
