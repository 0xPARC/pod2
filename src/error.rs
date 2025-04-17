use crate::middleware::{Statement, StatementTmpl};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    // Wrappers on top of other errors
    #[error("std::io::Error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("anyhow::Error: {0}")]
    Anyhow(#[from] anyhow::Error),
    #[error(transparent)]
    Infallible(#[from] std::convert::Infallible),

    // sub-categories of errors
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::error::TreeError),
    #[error(transparent)]
    Middleware(#[from] crate::middleware::error::MiddlewareError),

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
