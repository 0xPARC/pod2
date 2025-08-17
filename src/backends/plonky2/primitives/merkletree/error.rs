//! tree errors

use std::{backtrace::Backtrace, fmt::Debug};

pub type TreeResult<T, E = TreeError> = core::result::Result<T, E>;

#[derive(Debug, thiserror::Error)]
pub enum TreeInnerError {
    #[error("key not found")]
    KeyNotFound,
    #[error("key already exists")]
    KeyExists,
    #[error("max depth reached")]
    MaxDepth,
    #[error("proof of {0} does not verify")]
    ProofFail(String), // inclusion / exclusion
    #[error("invalid {0} proof")]
    InvalidProof(String),
    #[error("invalid state transition proof argument: {0}")]
    InvalidStateTransitionProogArg(String),
    #[error("state transition proof does not verify, reason: {0}")]
    StateTransitionProofFail(String),
    #[error("key too short (key length: {0}) for the max_depth: {1}")]
    TooShortKey(usize, usize),
}

#[derive(thiserror::Error)]
pub enum TreeError {
    #[error("Inner: {inner}\n{backtrace}")]
    Inner {
        inner: Box<TreeInnerError>,
        backtrace: Box<Backtrace>,
    },
    #[error("anyhow::Error: {0}")]
    Anyhow(#[from] anyhow::Error),
}

impl Debug for TreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

macro_rules! new {
    ($inner:expr) => {
        TreeError::Inner {
            inner: Box::new($inner),
            backtrace: Box::new(Backtrace::capture()),
        }
    };
}
use TreeInnerError::*;
impl TreeError {
    pub fn inner(&self) -> Option<&TreeInnerError> {
        match self {
            Self::Inner { inner, .. } => Some(inner),
            _ => None,
        }
    }
    pub(crate) fn key_not_found() -> Self {
        new!(KeyNotFound)
    }
    pub(crate) fn key_exists() -> Self {
        new!(KeyExists)
    }
    pub(crate) fn max_depth() -> Self {
        new!(MaxDepth)
    }
    pub(crate) fn proof_fail(obj: String) -> Self {
        new!(ProofFail(obj))
    }
    pub(crate) fn invalid_proof(obj: String) -> Self {
        new!(InvalidProof(obj))
    }
    pub(crate) fn invalid_state_transition_proof_arg(reason: String) -> Self {
        new!(InvalidStateTransitionProogArg(reason))
    }
    pub(crate) fn state_transition_fail(reason: String) -> Self {
        new!(StateTransitionProofFail(reason))
    }
    pub(crate) fn too_short_key(depth: usize, max_depth: usize) -> Self {
        new!(TooShortKey(depth, max_depth))
    }
}
