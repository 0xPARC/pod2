//! middleware errors

use crate::middleware::{Operation, PodId, PodType, Statement, StatementArg, Value};

pub type MiddlewareResult<T, E = MiddlewareError> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum MiddlewareError {
    #[error("type does not match, expected {0}, found {1}")]
    TypeNotEqual(PodType, Value),
    #[error("id does not match, expected {0}, found {1}")]
    IdNotEqual(PodId, PodId),
    #[error("invalid operation")]
    InvalidOp,
    #[error("incorrect statement args")]
    IncorrectStatementArgs,
    #[error("invalid deduction: {0:?} ⇏ {1:#}")]
    InvalidDeduction(Operation, Statement),
    #[error("statement argument {0:?} should be a {1}")]
    InvalidStatementArg(StatementArg, String),
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} amount of {1} should be {1} but it's {2}")]
    DiffAmount(String, String, usize, usize),

    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
    #[error("{0}")]
    Custom(String),
}

impl MiddlewareError {
    pub fn max_length(obj: String, found: usize, expect: usize) -> Self {
        Self::MaxLength(obj, found, expect)
    }
    pub fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        Self::DiffAmount(obj, unit, expect, found)
    }
    pub fn custom(s: String) -> Self {
        Self::Custom(s)
    }
}
