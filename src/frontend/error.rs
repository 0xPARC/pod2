use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{DynError, Statement, StatementTmpl};

pub type FrontendResult<T, E = FrontendError> = core::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} doesn't match {1}")]
    StatementsDontMatch(Statement, StatementTmpl),
    #[error("invalid arguments to {0} operation")]
    OpInvalidArgs(String),
    // Other
    #[error("{0}")]
    Custom(String),
}

#[derive(thiserror::Error)]
pub enum FrontendError {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<InnerError>,
        backtrace: Box<Backtrace>,
    },
    #[error(transparent)]
    Infallible(#[from] std::convert::Infallible),
    #[error(transparent)]
    Backend(#[from] Box<DynError>),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::MiddlewareError),
}

impl Debug for FrontendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        FrontendError::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use InnerError::*;
impl FrontendError {
    pub(crate) fn custom(s: String) -> Self {
        new!(Custom(s))
    }
    pub(crate) fn op_invalid_args(s: String) -> Self {
        new!(OpInvalidArgs(s))
    }
    pub(crate) fn statements_dont_match(s0: Statement, s1: StatementTmpl) -> Self {
        new!(StatementsDontMatch(s0, s1))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
}
