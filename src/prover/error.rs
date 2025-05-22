use std::sync::Arc;

use thiserror::Error;

use crate::frontend; // Import frontend error

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeferralReason {
    AmbiguousPrivateWildcard {
        wildcard_name: String,
        domain_size: usize,
    },
    AmbiguousSearchTarget {
        wildcard_name: String,
        domain_size: usize,
    },
    General(String),
}

impl std::fmt::Display for DeferralReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeferralReason::AmbiguousPrivateWildcard {
                wildcard_name,
                domain_size,
            } => {
                write!(f, "Private wildcard '{}' in custom predicate scope needs resolution (not singleton, domain size: {}).", wildcard_name, domain_size)
            }
            DeferralReason::AmbiguousSearchTarget {
                wildcard_name,
                domain_size,
            } => {
                write!(f, "Search target wildcard '{}' needs resolution (not singleton, domain size: {}).", wildcard_name, domain_size)
            }
            DeferralReason::General(msg) => write!(f, "{}", msg),
        }
    }
}

#[derive(Error, Debug, Clone)]
pub enum ProverError {
    #[error("I/O error: {0}")]
    Io(Arc<std::io::Error>),

    #[error("Serialization error: {0}")]
    Serialization(String),

    #[error("Frontend error during POD building: {0}")]
    FrontendError(Arc<frontend::Error>),

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

    #[error("Proof deferred: {0}")]
    ProofDeferred(DeferralReason),
}

impl From<std::io::Error> for ProverError {
    fn from(err: std::io::Error) -> Self {
        ProverError::Io(Arc::new(err))
    }
}

impl From<frontend::Error> for ProverError {
    fn from(err: frontend::Error) -> Self {
        ProverError::FrontendError(Arc::new(err))
    }
}
