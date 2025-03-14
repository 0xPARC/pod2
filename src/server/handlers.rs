use axum::Json;

use super::{error::ServerError, types::*};
use crate::{
    backends::plonky2::{mock_main::MockProver, mock_signed::MockSigner},
    frontend::{MainPod, MainPodBuilder, SignedPod, SignedPodBuilder},
    middleware::Params,
};

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
    let id = format!(
        "{:016x}{:016x}{:016x}{:016x}",
        pod.id().0 .0[0].0,
        pod.id().0 .0[1].0,
        pod.id().0 .0[2].0,
        pod.id().0 .0[3].0
    );
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

pub async fn create_main_pod(state: StateExtractor) -> Result<Json<MainPod>, ServerError> {
    let mut state = state.lock().await;
    let params = Params::default();
    let mut builder = MainPodBuilder::new(&params);

    // Create a prover and prove the pod
    let mut prover = MockProver {};
    let pod = builder
        .prove(&mut prover, &params)
        .map_err(ServerError::from)?;

    // Store the pod with its ID as a string
    let id = format!(
        "{:016x}{:016x}{:016x}{:016x}",
        pod.id().0 .0[0].0,
        pod.id().0 .0[1].0,
        pod.id().0 .0[2].0,
        pod.id().0 .0[3].0
    );
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
            let id = format!(
                "{:016x}{:016x}{:016x}{:016x}",
                pod.id().0 .0[0].0,
                pod.id().0 .0[1].0,
                pod.id().0 .0[2].0,
                pod.id().0 .0[3].0
            );
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
            let id = format!(
                "{:016x}{:016x}{:016x}{:016x}",
                pod.id().0 .0[0].0,
                pod.id().0 .0[1].0,
                pod.id().0 .0[2].0,
                pod.id().0 .0[3].0
            );
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

    // Create a temporary MainPod with the statements
    let mut main_pod = MainPod::new();
    for statement in req.statements {
        main_pod.add_statement(statement)?;
    }

    // Validate the MainPod
    let is_valid = main_pod.validate(&state.signed_pods)?;

    Ok(Json(is_valid))
}
