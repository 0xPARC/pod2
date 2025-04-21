use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{DynError, Statement, StatementTmpl};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    // Wrappers on top of other errors
    // #[error("std::io::Error: {0}")]
    // IOError(#[from] std::io::Error),
    // #[error("anyhow::Error: {0}")]
    // Anyhow(#[from] anyhow::Error),
    // #[error(transparent)]
    // Infallible(#[from] std::convert::Infallible),

    // sub-categories of errors
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::MiddlewareError),

    // Comparators errors
    #[error("not equal")]
    NotEqual,
    #[error("{0} {1} is over the limit {2}")]
    MaxLength(String, usize, usize),
    #[error("{0} amount of {1} should be {1} but it's {2}")]
    DiffAmount(String, String, usize, usize),

    // operation errors
    #[error("{0} doesn't match {1}")]
    StatementsDontMatch(Statement, StatementTmpl),
    #[error("invalid arguments to {0} operation")]
    OpInvalidArgs(String),

    // POD related
    #[error("invalid POD ID")]
    PodIdInvalid,
    #[error("verification failed: POD does not have type statement")]
    NotTypeStatement,
    #[error("repeated ValueOf")]
    RepeatedValueOf,
    #[error("Statement did not check")]
    StatementNotCheck,
    #[error("Key not found")]
    KeyNotFound,

    // Other
    #[error("{0}")]
    Custom(String),
    #[error("Plonky2 proof failed to verify")]
    Plonky2ProofFail,
}

#[derive(thiserror::Error)]
pub enum Error {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<InnerError>,
        backtrace: Box<Backtrace>,
    },
    // Wrappers on top of other errors
    #[error("std::io::Error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("anyhow::Error: {0}")]
    Anyhow(#[from] anyhow::Error),
    #[error(transparent)]
    Infallible(#[from] std::convert::Infallible),
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
    #[error(transparent)]
    Backend(#[from] Box<DynError>),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::MiddlewareError),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl Error {
    pub fn custom(s: String) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::Custom(s)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn plonky2_proof_fail() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::Plonky2ProofFail),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn key_not_found() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::KeyNotFound),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn statement_not_check() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::StatementNotCheck),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn repeated_value_of() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::RepeatedValueOf),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn not_type_statement() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::NotTypeStatement),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn pod_id_invalid() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::PodIdInvalid),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn op_invalid_args(s: String) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::OpInvalidArgs(s)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn statements_dont_match(s0: Statement, s1: StatementTmpl) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::StatementsDontMatch(s0, s1)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::DiffAmount(obj, unit, expect, found)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn max_length(obj: String, found: usize, expect: usize) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::MaxLength(obj, found, expect)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn not_equal() -> Self {
        Self::Inner {
            inner: Box::new(InnerError::NotEqual),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn middleware(e: crate::middleware::MiddlewareError) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::Middleware(e)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn tree(e: crate::backends::plonky2::primitives::merkletree::error::TreeError) -> Self {
        Self::Inner {
            inner: Box::new(InnerError::Tree(e)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn bar() -> Result<()> {
        Err(Error::not_equal())
    }

    fn foo() -> Result<()> {
        bar()
    }

    #[test]
    fn test_error_1() -> Result<()> {
        foo()
    }

    #[test]
    fn test_error_2() -> core::result::Result<(), InnerError> {
        Err(InnerError::NotEqual)
    }

    #[test]
    fn test_error_3() -> core::result::Result<(), anyhow::Error> {
        Err(anyhow::anyhow!("foo bar"))
    }
}
