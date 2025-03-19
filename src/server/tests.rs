use super::*;
use crate::backends::plonky2::mock_signed::MockSigner;
use crate::frontend::{
    AnchoredKey, Origin, PodClass, SignedPodBuilder, Statement, StatementArg, Value,
};
use crate::middleware::{NativePredicate, Params, PodId, Predicate};
use crate::prover::types::{
    WildcardAnchoredKey, WildcardId, WildcardStatementArg, WildcardTargetStatement,
};
use axum::{
    body::Body,
    http::{Request, StatusCode},
    routing::post,
    Router,
};
use serde_json::json;
use std::sync::Arc;
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
            "/api/validate-statements",
            post(handlers::validate_statements),
        )
        .with_state(state)
}

#[tokio::test]
async fn test_create_and_list_pods() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create a signed pod with nickname
        let signed_pod_req = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer",
                    "nickname": "test_pod",
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
        let created_pod: Pod = serde_json::from_slice(&body).unwrap();
        let created_id = match &created_pod.pod {
            PodVariant::Signed(pod) => format!("{:x}", pod.id()),
            PodVariant::Main(_) => panic!("Expected Signed pod"),
        };
        assert_eq!(created_pod.nickname, Some("test_pod".to_string()));

        // Create another pod without nickname
        let signed_pod_req2 = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer2",
                    "key_values": { "key2": "value2" }
                })
                .to_string(),
            ))
            .unwrap();

        let response = app.clone().oneshot(signed_pod_req2).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

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
        assert_eq!(pods.len(), 2, "Expected 2 pods in the list");

        // Verify the pods
        let pod_with_nickname = pods
            .iter()
            .find(|p| p.nickname == Some("test_pod".to_string()))
            .unwrap();
        let pod_without_nickname = pods.iter().find(|p| p.nickname.is_none()).unwrap();

        match &pod_with_nickname.pod {
            PodVariant::Signed(pod) => {
                let stored_id = format!("{:x}", pod.id());
                assert_eq!(
                    created_id, stored_id,
                    "Created pod ID does not match stored pod ID"
                );
            }
            PodVariant::Main(_) => panic!("Expected Signed pod"),
        }

        // Verify the pod without nickname
        match &pod_without_nickname.pod {
            PodVariant::Signed(pod) => {
                assert_eq!(
                    pod.kvs.get("key2"),
                    Some(&Value::String("value2".to_string())),
                    "Pod without nickname has incorrect key-value pair"
                );
            }
            PodVariant::Main(_) => panic!("Expected Signed pod"),
        }

        Ok(())
    })
    .await
}

#[tokio::test]
async fn test_duplicate_nickname() -> Result<(), Box<dyn std::error::Error>> {
    with_clean_state(|app| async move {
        // Create first pod with nickname
        let signed_pod_req = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer",
                    "nickname": "test_pod",
                    "key_values": { "key": "value" }
                })
                .to_string(),
            ))
            .unwrap();

        let response = app.clone().oneshot(signed_pod_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        // Try to create second pod with same nickname
        let signed_pod_req = Request::builder()
            .method("POST")
            .uri("/api/create-signed-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "signer": "test_signer",
                    "nickname": "test_pod",
                    "key_values": { "key": "value" }
                })
                .to_string(),
            ))
            .unwrap();

        let response = app.oneshot(signed_pod_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::INTERNAL_SERVER_ERROR);

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
                    "nickname": "test_pod",
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
        let pod: Pod = serde_json::from_slice(&body).unwrap();
        let pod_id = match &pod.pod {
            PodVariant::Signed(pod) => format!("{:x}", pod.id()),
            PodVariant::Main(_) => panic!("Expected Signed pod"),
        };
        println!(
            "DEBUG test_get_and_delete_pod - Created pod with ID: {}",
            pod_id
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
            pod_id
        );
        let response = app.clone().oneshot(get_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let retrieved_pod: Pod = serde_json::from_slice(&body).unwrap();
        assert_eq!(
            retrieved_pod.nickname,
            Some("test_pod".to_string()),
            "Retrieved pod nickname does not match"
        );

        // Delete the pod
        let delete_req = Request::builder()
            .method("POST")
            .uri("/api/delete-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(json!({ "id": pod_id }).to_string()))
            .unwrap();

        println!(
            "DEBUG test_get_and_delete_pod - Deleting pod with ID: {}",
            pod_id
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
            pod_id
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
        let signed_pod = signed_pod_builder.sign(&mut signer)?;
        let pod_id = format!("{:x}", signed_pod.id());
        println!("DEBUG test_import_pod - Created pod with ID: {}", pod_id);

        // Create the pod with nickname
        let pod = Pod {
            nickname: Some("test_pod".to_string()),
            pod: PodVariant::Signed(signed_pod.clone()),
        };

        // Import the pod
        let import_req = Request::builder()
            .method("POST")
            .uri("/api/import-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "pod": pod
                })
                .to_string(),
            ))
            .unwrap();

        println!("DEBUG test_import_pod - Importing pod with ID: {}", pod_id);
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
            pod_id
        );
        let response = app.oneshot(get_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);

        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let retrieved_pod: Pod = serde_json::from_slice(&body).unwrap();
        assert_eq!(
            retrieved_pod.nickname,
            Some("test_pod".to_string()),
            "Retrieved pod nickname does not match"
        );

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
        let statement = Statement {
            predicate: Predicate::Native(NativePredicate::ValueOf),
            args: vec![
                StatementArg::Key(AnchoredKey {
                    origin: Origin {
                        pod_id: pod.id(),
                        pod_class: PodClass::Signed,
                    },
                    key: "test_key".to_string(),
                }),
                StatementArg::Literal(Value::String("test_value".to_string())),
            ],
        };

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

        // Create the pod with no nickname
        let pod_wrapper = Pod {
            nickname: None,
            pod: PodVariant::Signed(pod.clone()),
        };

        // Import the pod into the server state
        let import_req = Request::builder()
            .method("POST")
            .uri("/api/import-pod")
            .header("Content-Type", "application/json")
            .body(Body::from(
                json!({
                    "pod": pod_wrapper
                })
                .to_string(),
            ))
            .unwrap();

        println!("DEBUG test_validate_statements - Importing pod into server state");
        let response = app.clone().oneshot(import_req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        println!("DEBUG test_validate_statements - Pod imported successfully");

        // Create a statement that checks if the pod's test_key equals "test_value"
        let statement = WildcardTargetStatement::Equal(
            WildcardAnchoredKey {
                wildcard_id: WildcardId::Concrete(Origin {
                    pod_id: pod.id(),
                    pod_class: PodClass::Signed,
                }),
                key: "test_key".to_string(),
            },
            WildcardStatementArg::Key(AnchoredKey {
                origin: Origin {
                    pod_id: pod.id(),
                    pod_class: PodClass::Signed,
                },
                key: "test_key".to_string(),
            }),
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
    use crate::prover::types::WildcardTargetStatement;

    let json = r#"{
  "Equal": [
    {
      "wildcard_id": {
        "type": "Concrete",
        "value": {
          "pod_class": "Signed",
          "pod_id": "5e7973ac718ad29817adf29a28ebe67e87ae945474ba3d1bdc903b7ff0e89f8a"
        }
      },
      "key": "test_key"
    },
    {
      "Key": {
        "origin": {
          "pod_class": "Signed",
          "pod_id": "5e7973ac718ad29817adf29a28ebe67e87ae945474ba3d1bdc903b7ff0e89f8a"
        },
        "key": "test_key"
      }
    }
  ]
}"#;

    let result = serde_json::from_str::<WildcardTargetStatement>(json);
    match result {
        Ok(stmt) => {
            println!("Successfully deserialized: {:?}", stmt);
            match stmt {
                WildcardTargetStatement::Equal(key, arg) => {
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
        WildcardAnchoredKey, WildcardId, WildcardStatementArg, WildcardTargetStatement,
    };

    // Create a concrete origin
    let origin = Origin {
        pod_id: PodId(hash_str("1234567890abcdef")),
        pod_class: PodClass::Signed,
    };

    // Create a wildcard anchored key
    let wildcard_key = WildcardAnchoredKey {
        wildcard_id: WildcardId::Concrete(origin.clone()),
        key: "test_key".to_string(),
    };

    // Create a concrete anchored key for the second argument
    let concrete_key = AnchoredKey {
        origin,
        key: "test_key".to_string(),
    };

    // Create the statement
    let statement =
        WildcardTargetStatement::Equal(wildcard_key, WildcardStatementArg::Key(concrete_key));

    // Serialize to JSON
    let json = serde_json::to_string_pretty(&statement).unwrap();
    println!("Serialized JSON:\n{}", json);

    // Try to deserialize it back
    let result = serde_json::from_str::<WildcardTargetStatement>(&json);
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
