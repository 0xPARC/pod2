use super::{error::ServerError, types::*};
use crate::{
    backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
    frontend::{
        serialization::{MainPodHelper, SignedPodHelper},
        MainPodBuilder, Operation, OperationArg, SignedPodBuilder, StatementArg,
    },
    middleware::{NativeOperation, OperationType, Params},
    prover::{engine::DeductionEngine, types::WildcardTargetStatement},
};
use axum::extract::{Json, State};
use serde::Deserialize;
use serde_json::{self, json};
use std::{collections::HashSet, sync::Arc};
use tokio::sync::Mutex;

#[derive(Debug, Deserialize)]
pub struct ValidateStatementsRequest {
    pub statements: Vec<WildcardTargetStatement>,
}

#[derive(Debug, Deserialize)]
pub struct UpdatePodNicknameRequest {
    pub id: String,
    pub nickname: Option<String>,
}

pub async fn list_pods(state: StateExtractor) -> Result<Json<Vec<Pod>>, ServerError> {
    let state = state.lock().await;
    let pods = state
        .db
        .list_pods()
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;
    Ok(Json(pods))
}

pub async fn get_pod(
    state: StateExtractor,
    Json(req): Json<GetPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    let state = state.lock().await;
    match state
        .db
        .get_pod(&req.id)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?
    {
        Some(pod) => Ok(Json(pod)),
        None => Err(ServerError::PodNotFound(req.id)),
    }
}

pub async fn create_signed_pod(
    State(state): State<Arc<Mutex<ServerState>>>,
    Json(req): Json<CreateSignedPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    // Check for duplicate nickname if one is provided
    if let Some(nickname) = &req.nickname {
        let state = state.lock().await;
        let existing_pods = state
            .db
            .list_pods()
            .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

        if existing_pods
            .iter()
            .any(|p| p.nickname.as_ref() == Some(nickname))
        {
            return Err(ServerError::DatabaseError(format!(
                "Pod with nickname '{}' already exists",
                nickname
            )));
        }
    }

    let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
    for (key, value) in req.key_values.iter() {
        signed_pod_builder.insert(key, value.clone());
    }
    let mut signer = MockSigner {
        pk: req.signer.into(),
    };
    let signed_pod = signed_pod_builder
        .sign(&mut signer)
        .map_err(|e| ServerError::DatabaseError(format!("Failed to sign pod: {}", e)))?;

    let pod = Pod {
        nickname: req.nickname,
        pod: PodVariant::Signed(signed_pod.clone()),
    };

    let id = format!("{:x}", signed_pod.id());
    let state = state.lock().await;
    state
        .db
        .store_pod(&id, &pod)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    Ok(Json(pod))
}

pub async fn create_main_pod(
    State(state): State<Arc<Mutex<ServerState>>>,
    Json(req): Json<CreateMainPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    // Validate that all referenced pods exist
    let state = state.lock().await;
    let pods = state
        .db
        .list_pods()
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    let mut engine = DeductionEngine::new();
    for pod in pods {
        match pod.pod {
            PodVariant::Signed(signed_pod) => engine.add_signed_pod(signed_pod),
            PodVariant::Main(main_pod) => engine.add_main_pod(main_pod),
        }
    }

    let proofs = engine.prove_multiple(req.statements.clone());
    if proofs.is_empty() {
        return Err(ServerError::DatabaseError(
            "No valid proofs found for statements".to_string(),
        ));
    }

    let mut added_pod_ids: HashSet<String> = HashSet::new();
    let mut ops = Vec::new();

    let mut builder = MainPodBuilder::new(&Params::default());
    for (_stmt, chain) in proofs.iter() {
        for (op_code, inputs, _output) in chain {
            let op = Operation(
                match op_code {
                    x if *x == NativeOperation::ContainsFromEntries as u8 => {
                        OperationType::Native(NativeOperation::ContainsFromEntries)
                    }
                    x if *x == NativeOperation::NotContainsFromEntries as u8 => {
                        OperationType::Native(NativeOperation::NotContainsFromEntries)
                    }
                    x if *x == NativeOperation::EqualFromEntries as u8 => {
                        OperationType::Native(NativeOperation::EqualFromEntries)
                    }
                    x if *x == NativeOperation::LtFromEntries as u8 => {
                        OperationType::Native(NativeOperation::LtFromEntries)
                    }
                    x if *x == NativeOperation::GtFromEntries as u8 => {
                        OperationType::Native(NativeOperation::GtFromEntries)
                    }
                    x if *x == NativeOperation::SumOf as u8 => {
                        OperationType::Native(NativeOperation::SumOf)
                    }
                    x if *x == NativeOperation::ProductOf as u8 => {
                        OperationType::Native(NativeOperation::ProductOf)
                    }
                    x if *x == NativeOperation::MaxOf as u8 => {
                        OperationType::Native(NativeOperation::MaxOf)
                    }
                    _ => panic!("Unknown operation code: {}", op_code),
                },
                inputs
                    .iter()
                    .map(|i| OperationArg::Statement(i.clone().into()))
                    .collect(),
            );
            ops.push(op.clone());
            for arg in op.1 {
                if let OperationArg::Statement(stmt) = arg {
                    for stmt_arg in stmt.args.iter() {
                        if let StatementArg::Key(key) = stmt_arg {
                            added_pod_ids.insert(format!("{:x}", key.origin.pod_id));
                        }
                    }
                }
            }
        }
    }

    for op in ops {
        // TODO not all ops should be public
        builder.pub_op(op).unwrap();
    }

    for pod_id in added_pod_ids {
        let pod = state.db.get_pod(&pod_id).unwrap();
        if pod.is_none() {
            return Err(ServerError::PodNotFound(pod_id));
        }
        let pod = pod.unwrap();
        match pod.pod {
            PodVariant::Signed(signed_pod) => builder.add_signed_pod(&signed_pod),
            PodVariant::Main(main_pod) => builder.add_main_pod(main_pod),
        }
    }

    let mut prover = MockProver {};
    let main_pod = builder
        .prove(&mut prover, &Params::default())
        .map_err(|e| ServerError::DatabaseError(format!("Failed to prove main pod: {}", e)))?;

    let pod = Pod {
        nickname: req.nickname,
        pod: PodVariant::Main(main_pod.clone()),
    };

    let id = format!("{:x}", main_pod.id());
    state
        .db
        .store_pod(&id, &pod)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    Ok(Json(pod))
}

pub async fn delete_pod(
    state: StateExtractor,
    Json(req): Json<DeletePodRequest>,
) -> Result<(), ServerError> {
    let state = state.lock().await;
    if state
        .db
        .delete_pod(&req.id)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?
    {
        Ok(())
    } else {
        Err(ServerError::PodNotFound(req.id))
    }
}

pub async fn import_pod(
    state: StateExtractor,
    Json(req): Json<ImportPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    let state = state.lock().await;
    let id = match &req.pod.pod {
        PodVariant::Signed(pod) => format!("{:x}", pod.id()),
        PodVariant::Main(pod) => format!("{:x}", pod.id()),
    };

    state
        .db
        .store_pod(&id, &req.pod)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    Ok(Json(req.pod))
}

pub async fn validate_statement(
    Json(_req): Json<ValidateStatementRequest>,
) -> Result<Json<bool>, ServerError> {
    // TODO: Implement actual statement validation
    Ok(Json(true))
}

pub async fn validate_statements(
    state: StateExtractor,
    Json(req): Json<ValidateStatementsRequest>,
) -> Result<Json<bool>, ServerError> {
    let state = state.lock().await;

    let mut engine = DeductionEngine::new();

    // Get all pods from database for validation
    let pods = state
        .db
        .list_pods()
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    for pod in pods {
        match pod.pod {
            PodVariant::Signed(signed_pod) => engine.add_signed_pod(signed_pod),
            PodVariant::Main(main_pod) => engine.add_main_pod(main_pod),
        }
    }

    let proofs = engine.prove_multiple(req.statements.clone());

    // Return true only if we found proofs for all statements
    Ok(Json(proofs.len() == req.statements.len()))
}

pub async fn get_schemas() -> Result<Json<serde_json::Value>, ServerError> {
    let schemas = json!({
        "SignedPod": schemars::schema_for!(SignedPodHelper),
        "MainPod": schemars::schema_for!(MainPodHelper),
        "FrontendWildcardStatement": schemars::schema_for!(WildcardTargetStatement),
        // Add any other schemas you want to expose
    });

    Ok(Json(schemas))
}

pub async fn export_pod(
    state: StateExtractor,
    axum::extract::Path(id): axum::extract::Path<String>,
) -> Result<Json<Pod>, ServerError> {
    let state = state.lock().await;
    match state
        .db
        .get_pod(&id)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?
    {
        Some(pod) => Ok(Json(pod)),
        None => Err(ServerError::PodNotFound(id)),
    }
}

pub async fn update_pod_nickname(
    state: StateExtractor,
    Json(req): Json<UpdatePodNicknameRequest>,
) -> Result<Json<Pod>, ServerError> {
    let state = state.lock().await;

    // Check for duplicate nickname if one is provided
    if let Some(nickname) = &req.nickname {
        let existing_pods = state
            .db
            .list_pods()
            .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

        if existing_pods.iter().any(|p| {
            let pod_id = match &p.pod {
                PodVariant::Signed(pod) => format!("{:x}", pod.id()),
                PodVariant::Main(pod) => format!("{:x}", pod.id()),
            };
            pod_id != req.id && p.nickname.as_ref() == Some(nickname)
        }) {
            return Err(ServerError::DatabaseError(format!(
                "Pod with nickname '{}' already exists",
                nickname
            )));
        }
    }

    // Get the existing pod
    let mut pod = state
        .db
        .get_pod(&req.id)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?
        .ok_or_else(|| ServerError::PodNotFound(req.id.clone()))?;

    // Update the nickname
    pod.nickname = req.nickname;

    // Store the updated pod
    state
        .db
        .store_pod(&req.id, &pod)
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    Ok(Json(pod))
}
