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

impl MiddlewareError {
    pub fn type_not_equal(expected: PodType, found: Value) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::TypeNotEqual(expected, found)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn id_not_equal(expected: PodId, found: PodId) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::IdNotEqual(expected, found)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn invalid_op() -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::InvalidOp),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn incorrect_statements_args() -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::IncorrectStatementArgs),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn invalid_deduction(op: Operation, st: Statement) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::IncorrectStatementArgs(op, st)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn invalid_statement_arg(st_arg: StatementArg, v: String) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::InvalidStatementArg(st_arg, v)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn max_length(obj: String, found: usize, expect: usize) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::MaxLength(obj, found, expect)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::DiffAmount(obj, unit, expect, found)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn custom(s: String) -> Self {
        Self::Inner {
            inner: Box::new(MiddlewareInnerError::Custom(s)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
}
