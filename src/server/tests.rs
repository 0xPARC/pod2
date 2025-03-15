use super::*;
use crate::backends::plonky2::mock_signed::MockSigner;
use crate::frontend::{
    AnchoredKey, Origin, PodClass, SignedPod, SignedPodBuilder, Statement, StatementArg, Value,
};
use crate::middleware::{NativePredicate, Params, PodId, Predicate};
use crate::prover::types::{
    FrontendWildcardStatement, WildcardAnchoredKey, WildcardId, WildcardStatementArg,
};
use axum::{
    body::Body,
    http::{Request, StatusCode},
    routing::post,
    Router,
};
use serde_json::json;
use std::fs;
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
    let result = f(app).await;
    result
}

async fn setup_test_app() -> Router {
    let state = Arc::new(Mutex::new(ServerState::new_with_path(":memory:").unwrap()));
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
        .route(
            "/api/validate-statements",
            post(handlers::validate_statements),
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

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let created_pod: SignedPod = serde_json::from_slice(&body).unwrap();
        let created_id = format!("{:x}", created_pod.id());
        println!(
            "DEBUG test_create_and_list_pods - Created pod with ID: {:?}",
            created_pod.id()
        );

        // List pods to verify storage
        let list_req = Request::builder()
            .method("POST")
            .uri("/api/list-pods")
            .header("Content-Type", "application/json")
            .body(Body::from("{}"))
            .unwrap();

        let response = app.clone().oneshot(list_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let pods: Vec<Pod> = serde_json::from_slice(&body).unwrap();
        assert_eq!(pods.len(), 1);

        // Verify the pod ID matches
        match &pods[0] {
            Pod::Signed(pod) => {
                let stored_id = format!("{:x}", pod.id());
                println!(
                    "DEBUG test_create_and_list_pods - Stored pod ID: {:?}",
                    pod.id()
                );
                assert_eq!(
                    created_id, stored_id,
                    "Created pod ID does not match stored pod ID"
                );
            }
            Pod::Main(_) => panic!("Expected Signed pod"),
        }

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
        let pod_id = format!("{:x}", pod.id());
        println!(
            "DEBUG test_get_and_delete_pod - Created pod with ID: {}",
            pod.id()
        );

        // Get the pod
        let get_req = Request::builder()
            .method("POST")
            .uri("/api/get-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(json!({ "id": pod_id }).to_string()))
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
            .body(Body::from(json!({ "id": pod_id }).to_string()))
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
            .body(Body::from(json!({ "id": pod_id }).to_string()))
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
        let pod_id = format!("{:x}", pod.id());
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
            .body(Body::from(json!({ "id": pod_id }).to_string()))
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

#[tokio::test]
async fn test_validate_statements() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        println!("DEBUG test_validate_statements - Starting test");

        // Create a test pod first
        let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
        signed_pod_builder.insert("test_key", "test_value");
        let mut signer = MockSigner {
            pk: "test_signer".into(),
        };
        let pod = signed_pod_builder.sign(&mut signer)?;
        println!(
            "DEBUG test_validate_statements - Created test pod with ID: {}",
            pod.id()
        );
        println!(
            "DEBUG test_validate_statements - Pod contents: {:?}",
            pod.kvs
        );

        // Import the pod into the server state
        let import_req = Request::builder()
            .method("POST")
            .uri("/api/import-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({ "pod": Pod::Signed(pod.clone()) }).to_string(),
            ))
            .unwrap();

        println!("DEBUG test_validate_statements - Importing pod into server state");
        let response = app.clone().oneshot(import_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        println!("DEBUG test_validate_statements - Pod imported successfully");

        // Create a statement that checks if the pod's test_key equals "test_value"
        let statement = FrontendWildcardStatement::Equal(
            WildcardAnchoredKey(
                WildcardId::Concrete(Origin(PodClass::Signed, pod.id())),
                "test_key".to_string(),
            ),
            WildcardStatementArg::Key(AnchoredKey(
                Origin(PodClass::Signed, pod.id()),
                "test_key".to_string(),
            )),
        );
        println!(
            "DEBUG test_validate_statements - Created statement: {:?}",
            statement
        );

        let statements = vec![statement];

        let validate_req = Request::builder()
            .method("POST")
            .uri("/api/validate-statements")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "statements": statements
                })
                .to_string(),
            ))
            .unwrap();

        println!("DEBUG test_validate_statements - Sending validation request");
        let response = app.oneshot(validate_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        println!("DEBUG test_validate_statements - Validation request successful");

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let result: bool = serde_json::from_slice(&body).unwrap();
        println!(
            "DEBUG test_validate_statements - Validation result: {}",
            result
        );
        assert!(result);

        Ok(())
    })
    .await
}

#[test]
fn test_frontend_wildcard_statement_deserialization() {
    use crate::frontend::{AnchoredKey, Origin, PodClass};
    use crate::middleware::hash_str;
    use crate::prover::types::{
        FrontendWildcardStatement, WildcardAnchoredKey, WildcardId, WildcardStatementArg,
    };

    // Create a valid PodId using hash_str
    let pod_id = hash_str("test_pod_id");

    let json = r#"{
        "Equal": [
            [
                {
                    "Concrete": [
                        "Signed",
                        "5e7973ac718ad29817adf29a28ebe67e87ae945474ba3d1bdc903b7ff0e89f8a"
                    ]
                },
                "test_key"
            ],
            {
                "Key": [
                    [
                        "Signed",
                        "5e7973ac718ad29817adf29a28ebe67e87ae945474ba3d1bdc903b7ff0e89f8a"
                    ],
                    "test_key"
                ]
            }
        ]
    }"#;

    let result = serde_json::from_str::<FrontendWildcardStatement>(json);
    match result {
        Ok(stmt) => {
            println!("Successfully deserialized: {:?}", stmt);
            match stmt {
                FrontendWildcardStatement::Equal(key, arg) => {
                    println!("First arg: {:?}", key);
                    println!("Second arg: {:?}", arg);
                }
                _ => panic!("Expected Equal statement"),
            }
        }
        Err(e) => {
            println!("Deserialization error: {}", e);
            panic!("Failed to deserialize");
        }
    }
}

#[test]
fn test_frontend_wildcard_statement_serialization() {
    use crate::frontend::{AnchoredKey, Origin, PodClass};
    use crate::middleware::hash_str;
    use crate::prover::types::{
        FrontendWildcardStatement, WildcardAnchoredKey, WildcardId, WildcardStatementArg,
    };

    // Create a concrete origin
    let origin = Origin(PodClass::Signed, PodId(hash_str("1234567890abcdef")));

    // Create a wildcard anchored key
    let wildcard_key =
        WildcardAnchoredKey(WildcardId::Concrete(origin.clone()), "test_key".to_string());

    // Create a concrete anchored key for the second argument
    let concrete_key = AnchoredKey(origin, "test_key".to_string());

    // Create the statement
    let statement =
        FrontendWildcardStatement::Equal(wildcard_key, WildcardStatementArg::Key(concrete_key));

    // Serialize to JSON
    let json = serde_json::to_string_pretty(&statement).unwrap();
    println!("Serialized JSON:\n{}", json);

    // Try to deserialize it back
    let result = serde_json::from_str::<FrontendWildcardStatement>(&json);
    match result {
        Ok(stmt) => {
            println!("Successfully deserialized: {:?}", stmt);
            assert_eq!(
                stmt, statement,
                "Deserialized statement should match original"
            );
        }
        Err(e) => {
            println!("Deserialization error: {}", e);
            panic!("Failed to deserialize");
        }
    }
}
