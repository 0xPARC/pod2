use anyhow::{anyhow, Result};
use std::fmt;

use super::{AnchoredKey, SignedPod, Value};
use crate::middleware::{self, hash_str, NativePredicate, Predicate};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementArg {
    Literal(Value),
    Key(AnchoredKey),
}

impl fmt::Display for StatementArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(v) => write!(f, "{}", v),
            Self::Key(r) => write!(f, "{}.{}", r.0 .1, r.1),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub Predicate, pub Vec<StatementArg>);

impl From<(&SignedPod, &str)> for Statement {
    fn from((pod, key): (&SignedPod, &str)) -> Self {
        // TODO: Actual value, TryFrom.
        let value_hash = pod.kvs().get(&hash_str(key)).cloned().unwrap();
        let value = pod
            .value_hash_map
            .get(&value_hash.into())
            .cloned()
            .unwrap_or(Value::Raw(value_hash));
        Statement(
            Predicate::Native(NativePredicate::ValueOf),
            vec![
                StatementArg::Key(AnchoredKey(pod.origin(), key.to_string())),
                StatementArg::Literal(value),
            ],
        )
    }
}

impl TryFrom<Statement> for middleware::Statement {
    type Error = anyhow::Error;
    fn try_from(s: Statement) -> Result<Self> {
        type MS = middleware::Statement;
        type NP = NativePredicate;
        type SA = StatementArg;
        let args = (
            s.1.get(0).cloned(),
            s.1.get(1).cloned(),
            s.1.get(2).cloned(),
        );
        Ok(match &s.0 {
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
                (NP::Contains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::Contains(ak1.into(), ak2.into())
                }
                (NP::NotContains, (Some(SA::Key(ak1)), Some(SA::Key(ak2)), None)) => {
                    MS::NotContains(ak1.into(), ak2.into())
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
                _ => Err(anyhow!("Ill-formed statement: {}", s))?,
            },
            Predicate::Custom(cpr) => MS::Custom(
                cpr.clone(),
                s.1.iter()
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
