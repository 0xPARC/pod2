//! middleware errors

use crate::middleware::{Operation, PodId, PodType, Statement, StatementArg, Value};

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
}
