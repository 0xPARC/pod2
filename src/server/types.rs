use axum::extract::State;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;

use crate::{
    frontend::{MainPod, SignedPod, Statement},
    prover::types::WildcardTargetStatement,
};

use super::storage;

// Types matching frontend
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pod {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nickname: Option<String>,
    #[serde(flatten)]
    pub pod: PodVariant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PodVariant {
    Signed(SignedPod),
    Main(MainPod),
}

// API request/response types
#[derive(Debug, Deserialize)]
pub struct GetPodRequest {
    pub id: String,
}

#[derive(Debug, Deserialize)]
pub struct CreateSignedPodRequest {
    pub signer: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nickname: Option<String>,
    pub key_values: crate::frontend::SignedPodValues,
}

#[derive(Debug, Deserialize)]
pub struct CreateMainPodRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nickname: Option<String>,
    pub statements: Vec<WildcardTargetStatement>,
}

#[derive(Debug, Deserialize)]
pub struct DeletePodRequest {
    pub id: String,
}

#[derive(Debug, Deserialize)]
pub struct ImportPodRequest {
    pub pod: Pod,
}

#[derive(Debug, Deserialize)]
pub struct ValidateStatementRequest {
    pub statement: Statement,
}

#[derive(Debug, Deserialize)]
pub struct ValidateStatementsRequest {
    pub statements: Vec<WildcardTargetStatement>,
}

// Server state
pub struct ServerState {
    pub db: storage::Database,
}

impl ServerState {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        Self::new_with_path("pods.db")
    }

    pub fn new_with_path(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            db: storage::Database::new(path)?,
        })
    }
}

// Type alias for state extractor
pub type StateExtractor = State<Arc<Mutex<ServerState>>>;
