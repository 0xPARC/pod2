use thiserror::Error;

#[derive(Error, Debug)]
pub enum SolverError {
    #[error("Internal solver error: {0}")]
    Internal(String),
}
