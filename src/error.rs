use std::backtrace::Backtrace;

use crate::middleware::{Statement, StatementTmpl};

pub type Result<T, E = ErrorBacktrace> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    // Wrappers on top of other errors
    // #[error("std::io::Error: {0}")]
    // IOError(#[from] std::io::Error),
    // #[error("anyhow::Error: {0}")]
    // Anyhow(#[from] anyhow::Error),
    // #[error(transparent)]
    // Infallible(#[from] std::convert::Infallible),

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

impl Error {
    pub fn custom(s: String) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::Custom(s))
    }
    pub fn plonky2_proof_fail() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::Plonky2ProofFail)
    }
    pub fn key_not_found() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::KeyNotFound)
    }
    pub fn statement_not_check() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::StatementNotCheck)
    }
    pub fn repeated_value_of() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::RepeatedValueOf)
    }
    pub fn not_type_statement() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::NotTypeStatement)
    }
    pub fn pod_id_invalid() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::PodIdInvalid)
    }
    pub fn op_invalid_args(s: String) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::OpInvalidArgs(s))
    }
    pub fn statements_dont_match(s0: Statement, s1: StatementTmpl) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::StatementsDontMatch(s0, s1))
    }
    pub fn diff_amount(obj: String, unit: String, expect: usize, found: usize) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::DiffAmount(obj, unit, expect, found))
    }
    pub fn max_length(obj: String, found: usize, expect: usize) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::MaxLength(obj, found, expect))
    }
    pub fn not_equal() -> ErrorBacktrace {
        ErrorBacktrace::from(Self::NotEqual())
    }
    pub fn middleware(e: crate::middleware::error::MiddlewareError) -> ErrorBacktrace {
        ErrorBacktrace::from(Self::Middleware(e))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ErrorBacktrace {
    #[error("{source}")]
    Inner {
        #[from]
        source: Error,
        backtrace: Backtrace,
    },
    // Wrappers on top of other errors
    #[error("std::io::Error: {0}")]
    IOError(#[from] std::io::Error),
    #[error("anyhow::Error: {0}")]
    Anyhow(#[from] anyhow::Error),
    #[error(transparent)]
    Infallible(#[from] std::convert::Infallible),
}

// pub fn err<T>(e: Error) -> Result<T> {
//     Err(ErrorBacktrace::from(e))
// }
