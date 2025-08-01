use std::{backtrace::Backtrace, fmt::Debug};

use crate::middleware::{PodId, PodType, Value};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum InnerError {
    #[error("id does not match, expected {0}, found {1}")]
    IdNotEqual(PodId, PodId),
    #[error("type does not match, expected {0}, found {1}")]
    TypeNotEqual(PodType, Value),
    #[error("signer public key does not match, expected {0}, found {1}")]
    SignerNotEqual(Value, Value),

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
}

#[derive(thiserror::Error)]
pub enum Error {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<InnerError>,
        backtrace: Box<Backtrace>,
    },
    #[error("anyhow::Error: {0}")]
    Anyhow(#[from] anyhow::Error),
    #[error("Plonky2 proof failed to verify {0}: {1}")]
    Plonky2ProofFail(String, anyhow::Error),
    #[error("base64::DecodeError: {0}")]
    Base64Decode(#[from] base64::DecodeError),
    #[error("serde_json::Error: {0}")]
    SerdeJson(#[from] serde_json::Error),
    #[error(transparent)]
    Tree(#[from] crate::backends::plonky2::primitives::merkletree::error::TreeError),
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
    pub fn custom(s: String) -> Self {
        new!(Custom(s))
    }
    pub fn plonky2_proof_fail(context: impl Into<String>, e: anyhow::Error) -> Self {
        Self::Plonky2ProofFail(context.into(), e)
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
    pub fn id_not_equal(expected: PodId, found: PodId) -> Self {
        new!(IdNotEqual(expected, found))
    }
    pub fn type_not_equal(expected: PodType, found: Value) -> Self {
        new!(TypeNotEqual(expected, found))
    }
    pub(crate) fn signer_not_equal(expected: Value, found: Value) -> Self {
        new!(SignerNotEqual(expected, found))
    }
}
