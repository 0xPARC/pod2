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
    #[error("reached empty node, should not have entered")]
    EmptyNode,
    #[error("proof of {0} does not verify")]
    ProofFail(String), // inclusion / exclusion
    #[error("invalid {0} proof")]
    InvalidProof(String),
    #[error("key too short (key length: {0}) for the max_depth: {1}")]
    TooShortKey(usize, usize),

    #[error("{0}")]
    Custom(String),
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
    pub fn key_not_found() -> Self {
        new!(KeyNotFound)
    }
    pub fn key_exists() -> Self {
        new!(KeyExists)
    }
    pub fn max_depth() -> Self {
        new!(MaxDepth)
    }
    pub fn empty_node() -> Self {
        new!(EmptyNode)
    }
    pub fn proof_fail(obj: String) -> Self {
        new!(ProofFail(obj))
    }
    pub fn invalid_proof(obj: String) -> Self {
        new!(InvalidProof(obj))
    }
    pub fn too_short_key(depth: usize, max_depth: usize) -> Self {
        new!(TooShortKey(depth, max_depth))
    }
    pub fn custom(s: String) -> Self {
        new!(Custom(s))
    }
}
