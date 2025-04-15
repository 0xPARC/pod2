use std::fmt;

// use serde::{Deserialize, Serialize};
use crate::{
    frontend::SignedPod,
    middleware::{AnchoredKey, OperationAux, OperationType, Statement, Value},
};

#[derive(Clone, Debug, PartialEq)]
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
        // TODO: TryFrom.
        let value = pod
            .kvs()
            .get(&key.into())
            .cloned()
            .unwrap_or_else(|| panic!("Key {} is not present in POD: {}", key, pod));
        Self::Statement(Statement::ValueOf(
            AnchoredKey::from((pod.id(), key)),
            value,
        ))
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

#[derive(Clone, Debug, PartialEq)]
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
