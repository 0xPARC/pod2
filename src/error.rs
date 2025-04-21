use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{DynError, Statement, StatementTmpl};

pub type Result<T, E = SuperError> = core::result::Result<T, E>;

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
pub enum SuperError {
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

impl Debug for SuperError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        SuperError::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use InnerError::*;
impl SuperError {
    pub fn custom(s: String) -> Self {
        new!(Custom(s))
    }
    pub fn plonky2_proof_fail() -> Self {
        new!(Plonky2ProofFail)
    }
    pub fn key_not_found() -> Self {
        new!(KeyNotFound)
    }
    pub fn statement_not_check() -> Self {
        new!(StatementNotCheck)
    }
    pub fn repeated_value_of() -> Self {
        new!(RepeatedValueOf)
    }
    pub fn not_type_statement() -> Self {
        new!(NotTypeStatement)
    }
    pub fn pod_id_invalid() -> Self {
        new!(PodIdInvalid)
    }
    pub fn op_invalid_args(s: String) -> Self {
        new!(OpInvalidArgs(s))
    }
    pub fn statements_dont_match(s0: Statement, s1: StatementTmpl) -> Self {
        new!(StatementsDontMatch(s0, s1))
    }
    pub fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        new!(DiffAmount(obj, unit, expect, found))
    }
    pub fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
    pub fn not_equal() -> Self {
        new!(NotEqual)
    }
    pub fn middleware(e: crate::middleware::MiddlewareError) -> Self {
        new!(Middleware(e))
    }
    pub fn tree(e: crate::backends::plonky2::primitives::merkletree::error::TreeError) -> Self {
        new!(Tree(e))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn bar() -> Result<()> {
        Err(SuperError::not_equal())
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
