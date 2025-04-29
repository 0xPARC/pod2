use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProverError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Serialization error: {0}")]
    Serialization(String), // Simplified example

    // Add necessary variants
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
    // Add other specific error types as needed
}
