//! tree errors

use std::{backtrace::Backtrace, fmt::Debug};

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
}

#[derive(thiserror::Error)]
#[error("Inner: {inner}\n{backtrace}")]
pub struct TreeError {
    inner: Box<TreeInnerError>,
    backtrace: Box<Backtrace>,
}

impl Debug for TreeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl TreeError {
    pub fn key_not_found() -> Self {
        Self {
            inner: Box::new(TreeInnerError::KeyNotFound),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn key_exists() -> Self {
        Self {
            inner: Box::new(TreeInnerError::KeyExists),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn max_depth() -> Self {
        Self {
            inner: Box::new(TreeInnerError::MaxDepth),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn empty_node() -> Self {
        Self {
            inner: Box::new(TreeInnerError::EmptyNode),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn proof_fail(obj: String) -> Self {
        Self {
            inner: Box::new(TreeInnerError::ProofFail(obj)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn invalid_proof(obj: String) -> Self {
        Self {
            inner: Box::new(TreeInnerError::InvalidProof(obj)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
    pub fn too_short_key(depth: usize, max_depth: usize) -> Self {
        Self {
            inner: Box::new(TreeInnerError::TooShortKey(depth, max_depth)),
            backtrace: Box::new(Backtrace::capture()),
        }
    }
}
