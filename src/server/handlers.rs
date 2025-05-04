use anyhow::Context;
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

// Use the ConnectionPool type alias from db
use crate::{backends::plonky2::mock::signedpod::MockSigner, frontend::{SignedPod, SignedPodBuilder}, server::db::ConnectionPool};
// Import necessary types for signing
use crate::middleware::Params;
use std::collections::HashMap;
use crate::middleware::{Hash, hash_str, Value as PodValue};

// Struct to represent a POD retrieved from the database
#[derive(Serialize, Deserialize)]
pub struct PodInfo {
    id: String,
    pod_type: String,
    pod_class: String,
    data: Value, // Deserialize blob into JSON Value
    label: Option<String>,
    created_at: String,
    space: String,
}

// Request body for the /api/pods/sign endpoint
#[derive(Deserialize)]
pub struct SignRequest {
    private_key: String,
    entries: HashMap<String, PodValue>, // Use the PodValue type
}

// Handler for GET /api/pods/:space
pub async fn list_pods_in_space(
    State(pool): State<ConnectionPool>,
    Path(space): Path<String>,
) -> Result<Json<Vec<PodInfo>>, AppError> {
    let conn = pool
        .get()
        .await
        .context("Failed to get DB connection from pool")?;

    let space_clone = space.clone(); // Clone space for the closure
    let pods = conn
        .interact(move |conn|
            // Query needs to be run in a blocking thread
            {
                let mut stmt = conn.prepare(
                    "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1",
                )?;
                let pod_iter = stmt.query_map([&space_clone], |row| {
                    let data_blob: Vec<u8> = row.get(3)?;
                    let data_value: Value = serde_json::from_slice(&data_blob).map_err(|e| {
                        rusqlite::Error::FromSqlConversionFailure(
                            3,
                            rusqlite::types::Type::Blob,
                            Box::new(e),
                        )
                    })?;

                    Ok(PodInfo {
                        id: row.get(0)?,
                        pod_type: row.get(1)?,
                        pod_class: row.get(2)?,
                        data: data_value,
                        label: row.get(4)?,
                        created_at: row.get(5)?,
                        space: row.get(6)?,
                    })
                })?;

                pod_iter.collect::<Result<Vec<_>, _>>()
            }
        )
        .await // Wait for the blocking operation
        // Explicitly format the error to ensure Send + Sync for anyhow::Error
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("Database interaction failed")? // Handle InteractError (now anyhow)
        .context(format!("Failed to query pods for space '{}'", space))?; // Handle inner rusqlite::Error

    Ok(Json(pods))
}

// Handler for GET /api/pods/:space/:id
pub async fn get_pod_by_id(
    State(pool): State<ConnectionPool>,
    Path((space, id)): Path<(String, String)>,
) -> Result<Json<PodInfo>, AppError> {
    let conn = pool
        .get()
        .await
        .context("Failed to get DB connection from pool")?;

    let space_clone = space.clone(); // Clone for the closure
    let id_clone = id.clone(); // Clone for the closure

    let pod_info_result = conn
        .interact(move |conn| -> anyhow::Result<PodInfo> { // Closure returns anyhow::Result
            let mut stmt = conn.prepare(
                "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            let pod_info = stmt.query_row([&space_clone, &id_clone], |row| {
                let data_blob: Vec<u8> = row.get(3)?;
                // Manually map serde_json error to rusqlite error for the closure
                let data_value: Value = serde_json::from_slice(&data_blob).map_err(|e| {
                    rusqlite::Error::FromSqlConversionFailure(
                        3, // Column index
                        rusqlite::types::Type::Blob,
                        Box::new(e),
                    )
                })?;

                Ok(PodInfo {
                    id: row.get(0)?,
                    pod_type: row.get(1)?,
                    pod_class: row.get(2)?,
                    data: data_value,
                    label: row.get(4)?,
                    created_at: row.get(5)?,
                    space: row.get(6)?,
                })
            });

            // Check for QueryReturnedNoRows specifically AFTER the query attempt
            match pod_info {
                Ok(pod) => Ok(pod),
                Err(rusqlite::Error::QueryReturnedNoRows) => {
                    // Return a custom error that indicates not found
                    Err(anyhow::anyhow!(rusqlite::Error::QueryReturnedNoRows))
                }
                Err(e) => Err(anyhow::Error::from(e).context("Failed during pod query_row")), // Wrap other rusqlite errors
            }
        })
        .await // Wait for the blocking operation
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e)) // Handle deadpool interact error
        .context("Database interaction failed")?;
        // Now pod_info_result is Result<PodInfo, anyhow::Error>

    // Check the result from interact for the specific NotFound error case
    match pod_info_result {
        Ok(pod) => Ok(Json(pod)),
        Err(err) => {
            // Check if the cause is rusqlite::Error::QueryReturnedNoRows
            if let Some(rusqlite_err) = err.downcast_ref::<rusqlite::Error>() {
                if matches!(rusqlite_err, rusqlite::Error::QueryReturnedNoRows) {
                    return Err(AppError::NotFound(format!(
                        "Pod with id '{}' not found in space '{}'",
                        id, space
                    )));
                }
            }
            // Otherwise, it's a different database error
            Err(AppError::DatabaseError(err))
        }
    }
}

// Handler for POST /api/pods/sign
pub async fn sign_pod(
    // Although we don't use the DB pool here, we keep it for consistency
    // State(_pool): State<ConnectionPool>,
    Json(payload): Json<SignRequest>,
) -> Result<Json<SignedPod>, AppError> {
    log::debug!("Received sign request: {:?}", "payload hidden"); // Avoid logging sensitive data like private keys

    // 1. Create signer
    // For now, using MockSigner directly with the provided string
    let mut signer = MockSigner { pk: payload.private_key };
    log::debug!("Created signer for pk: {}", signer.pk);

    // 2. Create builder
    let params = Params::default(); // Use default parameters for now
    let mut builder = SignedPodBuilder::new(&params);
    log::debug!("Created SignedPodBuilder");

    // 3. Add entries to builder
    for (key, value) in payload.entries {
        log::trace!("Inserting entry: key='{}', value=...", key); // Avoid logging potentially large values
        // The insert method handles the Value type directly.
        // We might need error handling if insert could fail, but current signature suggests not.
        builder.insert(&key, value);
    }
    log::debug!("Inserted all entries into builder");

    // 4. Sign the pod
    let signed_pod = builder.sign(&mut signer)
        .context("Failed to sign the POD")?; // Use anyhow context, convert to AppError via From
    log::debug!("Successfully signed POD with id: {}", signed_pod.id().0);

    // 5. Convert to helper for JSON serialization - NOT NEEDED due to #[serde(into)]
    // let helper: SignedPodHelper = signed_pod.into();

    // 6. Return the signed pod (Serde will use SignedPodHelper via .into())
    Ok(Json(signed_pod))
}

// Handler for POST /api/hash
pub async fn hash_string(body: String) -> Result<Json<Hash>, AppError> {
    log::debug!("Received hash request for string: {:?}", body);
    let hash_result = hash_str(&body);
    log::debug!("Computed hash: {}", hash_result);
    Ok(Json(hash_result))
}

// Updated error handling to distinguish Not Found from other errors
pub enum AppError {
    DatabaseError(anyhow::Error),
    NotFound(String),
}

// Tell axum how to convert `AppError` into a response.
impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        match self {
            AppError::DatabaseError(err) => {
                log::error!("Application error: {:#}", err);
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    format!("Something went wrong: {}", err),
                )
                    .into_response()
            }
            AppError::NotFound(msg) => {
                log::warn!("Resource not found: {}", msg);
                (StatusCode::NOT_FOUND, msg).into_response()
            }
        }
    }
}

// This enables using `?` on functions returning `Result<_, anyhow::Error>`
// to automatically convert them into AppError::DatabaseError.
// Note: This will NOT automatically handle rusqlite::Error::QueryReturnedNoRows
//       into AppError::NotFound. That needs explicit mapping.
impl From<anyhow::Error> for AppError {
    fn from(err: anyhow::Error) -> Self {
        AppError::DatabaseError(err)
    }
}

#[cfg(test)]
mod tests {
    use axum_test::TestServer;
    use chrono::Utc;
    use rusqlite::params;
    use serde_json::json;

    use super::*;
    use crate::{middleware::Key, server::{db::init_db_pool, routes::create_router}};

    // Helper to insert a test pod
    // Needs to take &mut Connection for interact
    async fn insert_test_pod(
        pool: &ConnectionPool,
        id: &str,
        pod_type: &str,
        pod_class: &str,
        data: &Value,
        label: Option<&str>,
        space: &str,
    ) {
        let conn = pool.get().await.unwrap();
        // Clone data to be owned by the closure
        let id_owned = id.to_string();
        let pod_type_owned = pod_type.to_string();
        let pod_class_owned = pod_class.to_string();
        let data_owned = data.clone();
        let label_owned = label.map(|s| s.to_string());
        let space_owned = space.to_string();

        conn.interact(move |conn| {
            let now = Utc::now().to_rfc3339();
            // Use owned data inside the closure
            let data_blob = serde_json::to_vec(&data_owned).unwrap(); 
            conn.execute(
                "INSERT INTO pods (id, pod_type, pod_class, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
                params![id_owned, pod_type_owned, pod_class_owned, data_blob, label_owned, now, space_owned],
            )
        })
        .await
        .unwrap()
        .unwrap();
    }

    // Helper to deserialize response (updated for axum_test::TestResponse)
    async fn response_to_pods(response: axum_test::TestResponse) -> Vec<PodInfo> {
        response.json() // TestResponse has a handy .json() method
    }

    #[tokio::test]
    async fn test_list_pods_in_space() {
        // 1. Setup: In-memory DB and router
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init db pool");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        // 2. Insert test data (no change needed here, uses helper)
        let pod1_data = json!({ "value": 1 });
        let pod2_data = json!({ "value": 2 });
        let pod3_data = json!({ "value": 3 });
        insert_test_pod(
            &pool,
            "id1",
            "main",
            "mock",
            &pod1_data,
            Some("label1"),
            "space1",
        )
        .await;
        insert_test_pod(&pool, "id2", "signed", "mock", &pod2_data, None, "space1").await;
        insert_test_pod(
            &pool,
            "id3",
            "main",
            "mock",
            &pod3_data,
            Some("label3"),
            "space2",
        )
        .await;

        // 3. Test: Get pods for space1 (no change needed)
        let response = server.get("/api/pods/space1").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 2);
        assert!(pods.iter().any(|p| p.id == "id1"
            && p.pod_type == "main"
            && p.label == Some("label1".to_string())
            && p.data == pod1_data
            && p.space == "space1"));
        assert!(pods.iter().any(|p| p.id == "id2"
            && p.pod_type == "signed"
            && p.label.is_none()
            && p.data == pod2_data
            && p.space == "space1"));
        assert!(pods[0].created_at.contains('T'));

        // 4. Test: Get pods for space2 (no change needed)
        let response = server.get("/api/pods/space2").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 1);
        assert_eq!(pods[0].id, "id3");
        assert_eq!(pods[0].pod_type, "main");
        assert_eq!(pods[0].label, Some("label3".to_string()));
        assert_eq!(pods[0].data, pod3_data);
        assert_eq!(pods[0].space, "space2");

        // 5. Test: Get pods for empty space (no change needed)
        let response = server.get("/api/pods/nonexistent_space").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;
        assert!(pods.is_empty());
    }

    #[tokio::test]
    async fn test_get_pod_by_id_success() {
        // Setup
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        // Insert test data
        let pod_data = json!({ "detail": "unique" });
        insert_test_pod(&pool, "test_id", "main", "mock", &pod_data, Some("test_label"), "test_space").await;

        // Test
        let response = server.get("/api/pods/test_space/test_id").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pod: PodInfo = response.json();

        assert_eq!(pod.id, "test_id");
        assert_eq!(pod.pod_type, "main");
        assert_eq!(pod.pod_class, "mock");
        assert_eq!(pod.data, pod_data);
        assert_eq!(pod.label, Some("test_label".to_string()));
        assert_eq!(pod.space, "test_space");
        assert!(pod.created_at.contains('T'));
    }

    #[tokio::test]
    async fn test_get_pod_by_id_not_found_in_space() {
        // Setup
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        // Insert test data in a different space
        let pod_data = json!({});
        insert_test_pod(&pool, "test_id", "main", "mock", &pod_data, None, "other_space").await;

        // Test requesting from the wrong space
        let response = server.get("/api/pods/test_space/test_id").await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains("Pod with id 'test_id' not found in space 'test_space'"));

    }

    #[tokio::test]
    async fn test_get_pod_by_id_not_found_id() {
        // Setup
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

         // Insert unrelated data
        let pod_data = json!({});
        insert_test_pod(&pool, "other_id", "main", "mock", &pod_data, None, "test_space").await;

        // Test requesting non-existent ID
        let response = server.get("/api/pods/test_space/non_existent_id").await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains("Pod with id 'non_existent_id' not found in space 'test_space'"));

    }

    #[tokio::test]
    async fn test_sign_pod_success() {
        // Setup: Router without DB (as sign doesn't use it)
        // We still need a pool, but it can be an empty in-memory one.
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        let router = create_router(pool.clone()); // Pass pool even if unused by handler
        let server = TestServer::new(router).unwrap();

        // Prepare request payload
        let request_payload = json!({
            "private_key": "my_secret_key",
            "entries": {
                "name": "Alice", // Serialized as Value::String
                "age": {"Int": "30"}, // Serialized as Value::Int
                "city": "Metropolis",
                "verified": true, // Serialized as Value::Bool
                "tags": ["a", "b", {"Int": "123"}] // Serialized as Value::Array
            }
        });

        // Send request
        let response = server.post("/api/pods/sign").json(&request_payload).await;

        // Assertions
        assert_eq!(response.status_code(), StatusCode::OK);

        // Deserialize response
        let response_pod: SignedPod = response.json();

        // Verify structure
        assert!(response_pod.verify().is_ok());

        // Verify entries (keys exist, basic structure check)
        assert_eq!(response_pod.kvs().len(), 7); // 5 entries + signer and type
        assert!(response_pod.kvs().contains_key(&Key::from("name")));
        assert!(response_pod.kvs().contains_key(&Key::from("age")));
        assert!(response_pod.kvs().contains_key(&Key::from("city")));
        assert!(response_pod.kvs().contains_key(&Key::from("verified")));
        assert!(response_pod.kvs().contains_key(&Key::from("tags")));

        // Deeper verification of entry values (optional but good)
        assert_eq!(response_pod.kvs().get(&Key::from("name")), Some(&PodValue::from("Alice")));
        assert_eq!(response_pod.kvs().get(&Key::from("age")), Some(&PodValue::from(30)));
        assert_eq!(response_pod.kvs().get(&Key::from("city")), Some(&PodValue::from("Metropolis")));
        assert_eq!(response_pod.kvs().get(&Key::from("verified")), Some(&PodValue::from(true)));
    }

    #[tokio::test]
    async fn test_hash_string_success() {
        // Setup: Router without DB
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        let input_string = "hello world";

        // Send request with plain text body
        let response = server
            .post("/api/hash")
            .content_type("text/plain") // Ensure correct content type
            .text(input_string.to_string()) // Use .text() for plain text body
            .await;

        // Assertions
        assert_eq!(response.status_code(), StatusCode::OK);

        // Deserialize response
        // Assuming Hash serialization works correctly (outputs a hex string in JSON)
        let response_hash: Hash = response.json();

        // Calculate expected hash locally
        let expected_hash = hash_str(input_string);

        // Verify the hash matches
        assert_eq!(response_hash, expected_hash);

        // Optional: Check the raw JSON if Hash serialization is known
        // let response_json: Value = response.json();
        // assert!(response_json.is_string());
        // let hash_str = response_json.as_str().unwrap();
        // assert_eq!(hash_str, hex::encode(expected_hash.value().to_bytes())); // Adjust based on actual serialization format
    }
}
