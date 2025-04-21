use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{DynError, PodId, PodType, Statement, StatementTmpl, Value};

pub type BackendResult<T, E = BackendError> = core::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    // sub-categories of errors
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::MiddlewareError),

    // Comparators errors
    #[error("not equal")]
    NotEqual,
    #[error("id does not match, expected {0}, found {1}")]
    IdNotEqual(PodId, PodId),
    #[error("type does not match, expected {0}, found {1}")]
    TypeNotEqual(PodType, Value),
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
pub enum BackendError {
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

impl Debug for BackendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        BackendError::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use InnerError::*;
impl BackendError {
    pub(crate) fn custom(s: String) -> Self {
        new!(Custom(s))
    }
    pub(crate) fn plonky2_proof_fail() -> Self {
        new!(Plonky2ProofFail)
    }
    pub(crate) fn key_not_found() -> Self {
        new!(KeyNotFound)
    }
    pub(crate) fn statement_not_check() -> Self {
        new!(StatementNotCheck)
    }
    pub(crate) fn repeated_value_of() -> Self {
        new!(RepeatedValueOf)
    }
    pub(crate) fn not_type_statement() -> Self {
        new!(NotTypeStatement)
    }
    pub(crate) fn pod_id_invalid() -> Self {
        new!(PodIdInvalid)
    }
    pub(crate) fn op_invalid_args(s: String) -> Self {
        new!(OpInvalidArgs(s))
    }
    pub(crate) fn statements_dont_match(s0: Statement, s1: StatementTmpl) -> Self {
        new!(StatementsDontMatch(s0, s1))
    }
    pub(crate) fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> Self {
        new!(DiffAmount(obj, unit, expect, found))
    }
    pub(crate) fn max_length(obj: String, found: usize, expect: usize) -> Self {
        new!(MaxLength(obj, found, expect))
    }
    pub(crate) fn not_equal() -> Self {
        new!(NotEqual)
    }
    pub(crate) fn id_not_equal(expected: PodId, found: PodId) -> Self {
        new!(IdNotEqual(expected, found))
    }
    pub(crate) fn type_not_equal(expected: PodType, found: Value) -> Self {
        new!(TypeNotEqual(expected, found))
    }
    pub(crate) fn middleware(e: crate::middleware::MiddlewareError) -> Self {
        new!(Middleware(e))
    }
    pub(crate) fn tree(
        e: crate::backends::plonky2::primitives::merkletree::error::TreeError,
    ) -> Self {
        new!(Tree(e))
    }
}
