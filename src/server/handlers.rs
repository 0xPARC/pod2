use super::{error::ServerError, types::*};
use crate::{
    backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
    frontend::{
        MainPod, MainPodBuilder, Operation, OperationArg, SignedPod, SignedPodBuilder, StatementArg,
    },
    middleware::{NativeOperation, OperationType, Params, PodId},
    prover::engine::DeductionEngine,
};
use axum::Json;
use std::collections::HashSet;

pub async fn list_pods(state: StateExtractor) -> Result<Json<Vec<Pod>>, ServerError> {
    let state = state.lock().await;
    let mut pods = Vec::new();

    pods.extend(state.signed_pods.values().cloned().map(Pod::Signed));
    pods.extend(state.main_pods.values().map(|pod| Pod::Main(pod.clone())));

    println!("DEBUG list_pods - Number of pods: {}", pods.len());
    println!(
        "DEBUG list_pods - Signed pod IDs: {:?}",
        state.signed_pods.keys().collect::<Vec<_>>()
    );
    println!(
        "DEBUG list_pods - Main pod IDs: {:?}",
        state.main_pods.keys().collect::<Vec<_>>()
    );

    // Add detailed logging for each pod's ID
    for pod in &pods {
        match pod {
            Pod::Signed(signed_pod) => {
                println!("DEBUG list_pods - Signed pod ID: {:?}", signed_pod.id());
            }
            Pod::Main(main_pod) => {
                println!("DEBUG list_pods - Main pod ID: {:?}", main_pod.id());
            }
        }
    }

    Ok(Json(pods))
}

pub async fn get_pod(
    state: StateExtractor,
    Json(req): Json<GetPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    let state = state.lock().await;
    println!("DEBUG get_pod - Requested ID: {}", req.id);
    println!(
        "DEBUG get_pod - Available signed pod IDs: {:?}",
        state.signed_pods.keys().collect::<Vec<_>>()
    );
    println!(
        "DEBUG get_pod - Available main pod IDs: {:?}",
        state.main_pods.keys().collect::<Vec<_>>()
    );

    if let Some(pod) = state.signed_pods.get(&req.id) {
        println!("DEBUG get_pod - Found signed pod with ID: {:?}", pod.id());
        Ok(Json(Pod::Signed(pod.clone())))
    } else if let Some(pod) = state.main_pods.get(&req.id) {
        println!("DEBUG get_pod - Found main pod with ID: {:?}", pod.id());
        Ok(Json(Pod::Main(pod.clone())))
    } else {
        println!("DEBUG get_pod - Pod not found");
        Err(ServerError::PodNotFound(req.id))
    }
}

pub async fn create_signed_pod(
    state: StateExtractor,
    Json(req): Json<CreateSignedPodRequest>,
) -> Result<Json<SignedPod>, ServerError> {
    let mut state = state.lock().await;

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

    // Store the pod with its ID as a string
    let id = format!("{:x}", pod.id());
    println!(
        "DEBUG create_signed_pod - Created pod with ID: {:?}",
        pod.id()
    );
    state.signed_pods.insert(id.clone(), pod.clone());
    println!(
        "DEBUG create_signed_pod - State now contains IDs: {:?}",
        state.signed_pods.keys().collect::<Vec<_>>()
    );
    Ok(Json(pod))
}

pub async fn create_main_pod(
    state: StateExtractor,
    Json(req): Json<CreateMainPodRequest>,
) -> Result<Json<MainPod>, ServerError> {
    let mut state = state.lock().await;
    let params = Params::default();
    let mut builder = MainPodBuilder::new(&params);

    let mut engine = DeductionEngine::new();
    for signed_pod in state.signed_pods.values() {
        println!(
            "DEBUG validate_statements - Adding signed pod to engine with ID: {}",
            signed_pod.id()
        );
        engine.add_signed_pod(signed_pod.clone());
    }

    println!("DEBUG validate_statements - Statements to validate:");
    for (i, stmt) in req.statements.iter().enumerate() {
        println!("DEBUG validate_statements - Statement {}: {:?}", i, stmt);
    }

    let proofs = engine.prove_multiple(req.statements);
    println!(
        "DEBUG validate_statements - Number of proofs found: {}",
        proofs.len()
    );

    if !proofs.is_empty() {
        let mut ops = Vec::new();
        let mut pod_ids: HashSet<PodId> = HashSet::new();
        for (stmt, chain) in proofs.iter() {
            for (op_code, inputs, output) in chain {
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
                println!("Adding op: {:?}", op);
                ops.push(op.clone());
                for arg in op.1 {
                    if let OperationArg::Statement(stmt) = arg {
                        for stmt_arg in stmt.1 {
                            if let StatementArg::Key(key) = stmt_arg {
                                pod_ids.insert(key.0 .1);
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
        println!("DEBUG create_main_pod - Pod IDs: {:?}", pod_ids);
        println!("DEBUG create_main_pod - State: {:?}", state.signed_pods);
        for pod_id in pod_ids {
            println!("DEBUG create_main_pod - Adding Pod ID: {:?}", pod_id);
            let id_string = format!("{:x}", pod_id);
            println!("DEBUG create_main_pod - ID String: {:?}", id_string);
            if let Some(pod) = state.signed_pods.get(&id_string) {
                builder.add_signed_pod(pod);
            }
            if let Some(pod) = state.main_pods.get(&id_string) {
                builder.add_main_pod(pod.clone());
            }
        }
    } else {
        println!("DEBUG validate_statements - No proofs found");
    }

    // Create a prover and prove the pod
    println!("DEBUG create_main_pod - Builder: {:?}", builder);
    let mut prover = MockProver {};
    let pod = builder
        .prove(&mut prover, &params)
        .map_err(ServerError::from)?;

    // Store the pod with its ID as a string
    let id = format!("{:x}", pod.id());
    println!(
        "DEBUG create_main_pod - Created pod with ID: {:?}",
        pod.id()
    );
    state.main_pods.insert(id.clone(), pod.clone());
    println!(
        "DEBUG create_main_pod - State now contains IDs: {:?}",
        state.main_pods.keys().collect::<Vec<_>>()
    );
    Ok(Json(pod))
}

pub async fn delete_pod(
    state: StateExtractor,
    Json(req): Json<DeletePodRequest>,
) -> Result<(), ServerError> {
    let mut state = state.lock().await;
    println!(
        "DEBUG delete_pod - Attempting to delete pod with ID: {}",
        req.id
    );
    println!(
        "DEBUG delete_pod - Available signed pod IDs: {:?}",
        state.signed_pods.keys().collect::<Vec<_>>()
    );
    println!(
        "DEBUG delete_pod - Available main pod IDs: {:?}",
        state.main_pods.keys().collect::<Vec<_>>()
    );

    if state.signed_pods.remove(&req.id).is_some() {
        println!("DEBUG delete_pod - Successfully deleted signed pod");
        Ok(())
    } else if state.main_pods.remove(&req.id).is_some() {
        println!("DEBUG delete_pod - Successfully deleted main pod");
        Ok(())
    } else {
        println!("DEBUG delete_pod - Pod not found for deletion");
        Err(ServerError::PodNotFound(req.id))
    }
}

pub async fn import_pod(
    state: StateExtractor,
    Json(req): Json<ImportPodRequest>,
) -> Result<Json<Pod>, ServerError> {
    let mut state = state.lock().await;

    match req.pod {
        Pod::Signed(pod) => {
            let id = format!("{:x}", pod.id());
            println!(
                "DEBUG import_pod - Importing signed pod with ID: {:?}",
                pod.id()
            );
            state.signed_pods.insert(id.clone(), pod.clone());
            println!(
                "DEBUG import_pod - State now contains signed pod IDs: {:?}",
                state.signed_pods.keys().collect::<Vec<_>>()
            );
            Ok(Json(Pod::Signed(pod)))
        }
        Pod::Main(pod) => {
            let id = format!("{:x}", pod.id());
            println!(
                "DEBUG import_pod - Importing main pod with ID: {:?}",
                pod.id()
            );
            state.main_pods.insert(id.clone(), pod.clone());
            println!(
                "DEBUG import_pod - State now contains main pod IDs: {:?}",
                state.main_pods.keys().collect::<Vec<_>>()
            );
            Ok(Json(Pod::Main(pod)))
        }
    }
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

    println!("DEBUG validate_statements - Starting validation");
    println!(
        "DEBUG validate_statements - Number of statements to validate: {}",
        req.statements.len()
    );
    println!(
        "DEBUG validate_statements - Number of signed pods in state: {}",
        state.signed_pods.len()
    );

    let mut engine = DeductionEngine::new();
    for signed_pod in state.signed_pods.values() {
        println!(
            "DEBUG validate_statements - Adding signed pod to engine with ID: {}",
            signed_pod.id()
        );
        engine.add_signed_pod(signed_pod.clone());
    }

    let proofs = engine.prove_multiple(req.statements);

    if !proofs.is_empty() {
        println!("DEBUG validate_statements - Proofs found:");
        for (i, (stmt, chain)) in proofs.iter().enumerate() {
            println!("DEBUG validate_statements - Proof {}:", i);
            println!("DEBUG validate_statements -   Statement: {:?}", stmt);
            println!(
                "DEBUG validate_statements -   Chain length: {}",
                chain.len()
            );
            for (j, (op, inputs, output)) in chain.iter().enumerate() {
                println!(
                    "DEBUG validate_statements -   Step {}: Operation {:?}",
                    j, op
                );
                println!("DEBUG validate_statements -     Inputs: {:?}", inputs);
                println!("DEBUG validate_statements -     Output: {:?}", output);
            }
        }
    } else {
        println!("DEBUG validate_statements - No proofs found");
    }

    // Return true only if we found proofs for all statements
    Ok(Json(!proofs.is_empty()))
}
