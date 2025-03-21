use super::Statement;
use crate::middleware::{self, OperationType, Params, ToFields, F};
use anyhow::Result;
use plonky2::field::types::{Field, PrimeField64};
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationArg {
    None,
    Index(usize),
}

impl ToFields for OperationArg {
    fn to_fields(&self, _params: &Params) -> Vec<F> {
        let f = match self {
            Self::None => F::ZERO,
            Self::Index(i) => F::from_canonical_usize(*i),
        };
        vec![f]
    }
}

impl OperationArg {
    pub fn is_none(&self) -> bool {
        matches!(self, OperationArg::None)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Operation(pub OperationType, pub Vec<OperationArg>);

impl Operation {
    pub fn op_type(&self) -> OperationType {
        self.0.clone()
    }
    pub fn args(&self) -> &[OperationArg] {
        &self.1
    }
    pub fn deref(&self, statements: &[Statement]) -> Result<crate::middleware::Operation> {
        let deref_args = self
            .1
            .iter()
            .flat_map(|arg| match arg {
                OperationArg::None => None,
                OperationArg::Index(i) => Some(statements[*i].clone().try_into()),
            })
            .collect::<Result<Vec<crate::middleware::Statement>>>()?;
        middleware::Operation::op(self.0.clone(), &deref_args)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} ", self.0)?;
        for (i, arg) in self.1.iter().enumerate() {
            if !(!f.alternate() && arg.is_none()) {
                if i != 0 {
                    write!(f, " ")?;
                }
                match arg {
                    OperationArg::None => write!(f, "none")?,
                    OperationArg::Index(i) => write!(f, "{:02}", i)?,
                }
            }
        }
        Ok(())
    }
}
