use thiserror::Error;

use crate::frontend; // Import frontend error

#[derive(Error, Debug)]
pub enum ProverError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Serialization error: {0}")]
    Serialization(String),

    #[error("Frontend error during POD building: {0}")]
    FrontendError(#[from] frontend::Error),

    #[error("Feature not implemented: {0}")]
    NotImplemented(String),

    #[error("Prover configuration error: {0}")]
    Configuration(String),

    #[error("Proof request unsatisfiable: {0}")]
    Unsatisfiable(String),

    #[error("Inconsistent wildcard usage: {0}")]
    InconsistentWildcard(String),

    #[error("Internal prover error: {0}")]
    Internal(String),

    #[error("An unexpected error occurred: {0}")]
    Other(String),

    #[error("Maximum recursion depth exceeded: {0}")]
    MaxDepthExceeded(String),

    #[error("Proof deferred due to unresolved ambiguity: {0}")]
    ProofDeferred(String),
}
