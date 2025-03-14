use axum::extract::State;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;

use crate::{
    frontend::{MainPod, SignedPod, Statement},
    prover::types::FrontendWildcardStatement,
};

// Types matching frontend
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Pod {
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
    pub key_values: crate::frontend::SignedPodValues,
}

#[derive(Debug, Deserialize)]
pub struct CreateMainPodRequest {
    pub statements: Vec<FrontendWildcardStatement>,
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
    pub statements: Vec<FrontendWildcardStatement>,
}

// Server state
#[derive(Default)]
pub struct ServerState {
    pub signed_pods: std::collections::HashMap<String, SignedPod>,
    pub main_pods: std::collections::HashMap<String, MainPod>,
}

impl ServerState {
    pub fn new() -> Self {
        Self::default()
    }
}

// Type alias for state extractor
pub type StateExtractor = State<Arc<Mutex<ServerState>>>;
