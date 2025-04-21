//! middleware errors

use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{Operation, PodId, PodType, Statement, StatementArg, Value};

pub type MiddlewareResult<T, E = MiddlewareError> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum MiddlewareInnerError {
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

    #[error("{0}")]
    Custom(String),
}

#[derive(thiserror::Error)]
pub enum MiddlewareError {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<MiddlewareInnerError>,
        backtrace: Box<Backtrace>,
    },
    // Wrappers on top of other errors
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
}

impl Debug for MiddlewareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        MiddlewareError::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use MiddlewareInnerError::*;
impl MiddlewareError {
    pub(crate) fn type_not_equal(expected: PodType, found: Value) -> Self {
        new!(TypeNotEqual(expected, found))
    }
    pub(crate) fn id_not_equal(expected: PodId, found: PodId) -> Self {
        new!(IdNotEqual(expected, found))
    }
    pub(crate) fn invalid_op() -> Self {
        new!(InvalidOp)
    }
    pub(crate) fn incorrect_statements_args() -> Self {
        new!(IncorrectStatementArgs)
    }
    pub(crate) fn invalid_deduction(op: Operation, st: Statement) -> Self {
        new!(InvalidDeduction(op, st))
    }
    pub(crate) fn invalid_statement_arg(st_arg: StatementArg, v: String) -> Self {
        new!(InvalidStatementArg(st_arg, v))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
    pub(crate) fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        new!(DiffAmount(obj, unit, expect, found))
    }
    pub(crate) fn custom(s: String) -> Self {
        new!(Custom(s))
    }
}
