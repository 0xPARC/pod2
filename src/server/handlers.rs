use super::{error::ServerError, types::*};
use crate::{
    backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
    frontend::{
        serialization::{MainPodHelper, SignedPodHelper},
        MainPod, MainPodBuilder, Operation, OperationArg, SignedPod, SignedPodBuilder,
        StatementArg,
    },
    middleware::{NativeOperation, OperationType, Params, PodId},
    prover::{engine::DeductionEngine, types::FrontendWildcardStatement},
};
use axum::Json;
use serde_json::{self, json};
use std::collections::HashSet;

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
    state: StateExtractor,
    Json(req): Json<CreateSignedPodRequest>,
) -> Result<Json<SignedPod>, ServerError> {
    let state = state.lock().await;

    // Create a signed pod using the frontend's builder
    let params = Params::default();
    let mut builder = SignedPodBuilder::new(&params);

    // Add the key values to the builder
    for (key, value) in req.key_values.iter() {
        builder.insert(key, value.clone());
    }

    // Sign the pod with the provided signer
    let mut signer = MockSigner { pk: req.signer };
    let pod = builder.sign(&mut signer).map_err(ServerError::from)?;

    // Store the pod
    let id = format!("{:x}", pod.id());
    state
        .db
        .store_pod(&id, &Pod::Signed(pod.clone()))
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    Ok(Json(pod))
}

pub async fn create_main_pod(
    state: StateExtractor,
    Json(req): Json<CreateMainPodRequest>,
) -> Result<Json<MainPod>, ServerError> {
    let state = state.lock().await;
    let params = Params::default();
    let mut builder = MainPodBuilder::new(&params);

    let mut engine = DeductionEngine::new();

    // Get all pods from database for validation
    let pods = state
        .db
        .list_pods()
        .map_err(|e| ServerError::DatabaseError(e.to_string()))?;

    for pod in pods {
        if let Pod::Signed(signed_pod) = pod {
            engine.add_signed_pod(signed_pod);
        }
    }

    let proofs = engine.prove_multiple(req.statements);

    if !proofs.is_empty() {
        let mut pod_ids: HashSet<PodId> = HashSet::new();
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

                // Extract pod IDs before moving op
                for arg in op.1.iter() {
                    if let OperationArg::Statement(stmt) = arg {
                        for stmt_arg in &stmt.args {
                            if let StatementArg::Key(key) = stmt_arg {
                                pod_ids.insert(key.origin.pod_id);
                            }
                        }
                    }
                }

                builder.pub_op(op).unwrap();
            }
        }

        for pod_id in pod_ids {
            let id_string = format!("{:x}", pod_id);
            if let Ok(Some(Pod::Signed(pod))) = state.db.get_pod(&id_string) {
                builder.add_signed_pod(&pod);
            }
            if let Ok(Some(Pod::Main(pod))) = state.db.get_pod(&id_string) {
                builder.add_main_pod(pod);
            }
        }
    }

    let mut prover = MockProver {};
    let pod = builder
        .prove(&mut prover, &params)
        .map_err(ServerError::from)?;

    // Store the pod
    let id = format!("{:x}", pod.id());
    state
        .db
        .store_pod(&id, &Pod::Main(pod.clone()))
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
    let id = match &req.pod {
        Pod::Signed(pod) => format!("{:x}", pod.id()),
        Pod::Main(pod) => format!("{:x}", pod.id()),
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
        if let Pod::Signed(signed_pod) = pod {
            engine.add_signed_pod(signed_pod);
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
        "FrontendWildcardStatement": schemars::schema_for!(FrontendWildcardStatement),
        // Add any other schemas you want to expose
    });

    Ok(Json(schemas))
}
