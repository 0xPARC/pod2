use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum ProverError {
    #[error("Generic prover error: {0}")]
    Generic(String),
    // Add more specific error types as needed
}
