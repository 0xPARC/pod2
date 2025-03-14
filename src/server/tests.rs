use super::*;
use crate::backends::plonky2::mock_signed::MockSigner;
use crate::frontend::{
    AnchoredKey, Origin, PodClass, SignedPod, SignedPodBuilder, Statement, StatementArg, Value,
};
use crate::middleware::{NativePredicate, Params, Predicate};
use axum::{
    body::Body,
    http::{Request, StatusCode},
    routing::post,
    Router,
};
use serde_json::json;
use std::{collections::HashMap, sync::Arc};
use tokio::sync::Mutex;
use tower::ServiceExt;

// Helper to ensure clean state for each test
async fn with_clean_state<F, Fut>(f: F) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnOnce(Router) -> Fut,
    Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
{
    let app = setup_test_app().await;
    f(app).await
}

async fn setup_test_app() -> Router {
    let state = Arc::new(Mutex::new(ServerState::new()));
    Router::new()
        .route("/api/list-pods", post(handlers::list_pods))
        .route("/api/get-pod", post(handlers::get_pod))
        .route("/api/create-signed-pod", post(handlers::create_signed_pod))
        .route("/api/create-main-pod", post(handlers::create_main_pod))
        .route("/api/delete-pod", post(handlers::delete_pod))
        .route("/api/import-pod", post(handlers::import_pod))
        .route(
            "/api/validate-statement",
            post(handlers::validate_statement),
        )
        .with_state(state)
}

#[tokio::test]
async fn test_create_and_list_pods() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create a signed pod
        let signed_pod_req = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer",
                    "key_values": { "key": "value" }
                })
                .to_string(),
            ))
            .unwrap();

        let response = app.clone().oneshot(signed_pod_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // Create a main pod
        let main_pod_req = Request::builder()
            .method("POST")
            .uri("/api/create-main-pod")
            .header("Content-Type", "application/json")
            .body(Body::from("{}"))
            .unwrap();

        let response = app.clone().oneshot(main_pod_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // List pods
        let list_req = Request::builder()
            .method("POST")
            .uri("/api/list-pods")
            .header("Content-Type", "application/json")
            .body(Body::from("{}"))
            .unwrap();

        let response = app.oneshot(list_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let pods: Vec<Pod> = serde_json::from_slice(&body).unwrap();
        assert_eq!(pods.len(), 2);

        Ok(())
    })
    .await
}

#[tokio::test]
async fn test_get_and_delete_pod() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create a signed pod
        let create_req = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer",
                    "key_values": { "key": "value" }
                })
                .to_string(),
            ))
            .unwrap();

        let response = app.clone().oneshot(create_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let pod: SignedPod = serde_json::from_slice(&body).unwrap();
        println!(
            "DEBUG test_get_and_delete_pod - Created pod with ID: {}",
            pod.id()
        );

        // Get the pod
        let get_req = Request::builder()
            .method("POST")
            .uri("/api/get-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "id": pod.id().to_string() }).to_string(),
            ))
            .unwrap();

        println!(
            "DEBUG test_get_and_delete_pod - Requesting pod with ID: {}",
            pod.id()
        );
        let response = app.clone().oneshot(get_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // Delete the pod
        let delete_req = Request::builder()
            .method("POST")
            .uri("/api/delete-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "id": pod.id().to_string() }).to_string(),
            ))
            .unwrap();

        println!(
            "DEBUG test_get_and_delete_pod - Deleting pod with ID: {}",
            pod.id()
        );
        let response = app.clone().oneshot(delete_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // Try to get the deleted pod
        let get_req = Request::builder()
            .method("POST")
            .uri("/api/get-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "id": pod.id().to_string() }).to_string(),
            ))
            .unwrap();

        println!(
            "DEBUG test_get_and_delete_pod - Requesting deleted pod with ID: {}",
            pod.id()
        );
        let response = app.oneshot(get_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::NOT_FOUND);

        Ok(())
    })
    .await
}

#[tokio::test]
async fn test_import_pod() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create a pod to import
        let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
        signed_pod_builder.insert("key", "value");
        let mut signer = MockSigner {
            pk: "test_signer".into(),
        };
        let pod = signed_pod_builder.sign(&mut signer)?;
        println!("DEBUG test_import_pod - Created pod with ID: {}", pod.id());

        // Import the pod
        let import_req = Request::builder()
            .method("POST")
            .uri("/api/import-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "pod": Pod::Signed(pod.clone()) }).to_string(),
            ))
            .unwrap();

        println!(
            "DEBUG test_import_pod - Importing pod with ID: {}",
            pod.id()
        );
        let response = app.clone().oneshot(import_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // Verify the pod was imported
        let get_req = Request::builder()
            .method("POST")
            .uri("/api/get-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "id": pod.id().to_string() }).to_string(),
            ))
            .unwrap();

        println!(
            "DEBUG test_import_pod - Requesting imported pod with ID: {}",
            pod.id()
        );
        let response = app.oneshot(get_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        Ok(())
    })
    .await
}

#[tokio::test]
async fn test_validate_statement() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create a test pod first
        let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
        signed_pod_builder.insert("test_key", "test_value");
        let mut signer = MockSigner {
            pk: "test_signer".into(),
        };
        let pod = signed_pod_builder.sign(&mut signer)?;

        // Create a statement that checks if the pod's test_key equals "test_value"
        let statement = Statement(
            Predicate::Native(NativePredicate::ValueOf),
            vec![
                StatementArg::Key(AnchoredKey(
                    Origin(PodClass::Signed, pod.id()),
                    "test_key".to_string(),
                )),
                StatementArg::Literal(Value::String("test_value".to_string())),
            ],
        );

        let validate_req = Request::builder()
            .method("POST")
            .uri("/api/validate-statement")
            .header("Content-Type", "application/json")
            .body(Body::from(json!({ "statement": statement }).to_string()))
            .unwrap();

        let response = app.oneshot(validate_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let result: bool = serde_json::from_slice(&body).unwrap();
        assert!(result);

        Ok(())
    })
    .await
}
