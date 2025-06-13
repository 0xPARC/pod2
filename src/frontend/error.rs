use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{DynError, Statement, StatementTmpl, WildcardValue};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} doesn't match {1:#}.  Wildcard map: {2:?}")]
    StatementsDontMatch(Statement, StatementTmpl, Vec<Option<WildcardValue>>),
    #[error("invalid arguments to {0} operation")]
    OpInvalidArgs(String),
    // Other
    #[error("{0}")]
    Custom(String),
}

#[derive(thiserror::Error)]
pub enum Error {
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
    Middleware(#[from] crate::middleware::Error),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        Error::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use InnerError::*;
impl Error {
    pub(crate) fn custom(s: impl Into<String>) -> Self {
        new!(Custom(s.into()))
    }
    pub(crate) fn op_invalid_args(s: String) -> Self {
        new!(OpInvalidArgs(s))
    }
    pub(crate) fn statements_dont_match(
        s0: Statement,
        s1: StatementTmpl,
        wc_map: Vec<Option<WildcardValue>>,
    ) -> Self {
        new!(StatementsDontMatch(s0, s1, wc_map))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
}
