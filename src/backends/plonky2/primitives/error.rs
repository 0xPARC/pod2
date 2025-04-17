//! tree errors
#[derive(Debug, thiserror::Error)]
pub enum TreeError {
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
