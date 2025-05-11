use anyhow::Context;
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use chrono::Utc;

use crate::{backends::plonky2::mock::signedpod::MockSigner, frontend::{SignedPod, SignedPodBuilder}, server::db::ConnectionPool};
use crate::middleware::{Hash, hash_str, Value as PodValue}; 

use super::AppError; 

#[derive(Serialize, Deserialize)]
pub struct PodInfo {
    pub id: String,
    pub pod_type: String,
    pub pod_class: String,
    pub data: Value, // Deserialize blob into JSON Value
    pub label: Option<String>,
    pub created_at: String,
    pub space: String,
}

// Request body for the /api/pods/sign endpoint
#[derive(Deserialize)]
pub struct SignRequest {
    private_key: String,
    entries: std::collections::HashMap<String, PodValue>, // Use the PodValue type
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct ImportPodRequest {
    pod_type: String,
    pod_class: String,
    data: serde_json::Value,
    label: Option<String>,
}

// Handler for POST /api/pods/:space_id/:pod_id
pub async fn import_pod_to_space(
    State(pool): State<ConnectionPool>,
    Path((space_id, pod_id)): Path<(String, String)>,
    Json(payload): Json<ImportPodRequest>,
) -> Result<impl IntoResponse, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;
    
    let data_blob = serde_json::to_vec(&payload.data)
        .context("Failed to serialize pod data to JSON for storage")?;
    let now = Utc::now().to_rfc3339();

    let space_exists_conn = pool.get().await.context("Failed to get DB connection for space check")?;
    let space_id_check_clone = space_id.clone();
    let space_exists = space_exists_conn
        .interact(move |conn| {
            let mut stmt = conn.prepare("SELECT 1 FROM spaces WHERE id = ?1")?;
            stmt.exists([space_id_check_clone])
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("DB interaction failed for space existence check")?
        .context("Failed to check if space exists")?;

    if !space_exists {
        return Err(AppError::NotFound(format!("Space with id '{}' not found", space_id)));
    }
    
    let space_id_clone = space_id.clone();
    let pod_id_clone = pod_id.clone();
    let pod_type_clone = payload.pod_type.clone();
    let pod_class_clone = payload.pod_class.clone();
    let label_clone = payload.label.clone();

    conn.interact(move |conn| {
        conn.execute(
            "INSERT INTO pods (id, pod_type, pod_class, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            rusqlite::params![pod_id_clone, pod_type_clone, pod_class_clone, data_blob, label_clone, now, space_id_clone],
        )
    })
    .await
    .map_err(|e| anyhow::anyhow!("InteractError: {}", e)) 
    .context("DB interaction failed for import_pod_to_space")?
    .context(format!("Failed to import pod '{}' into space '{}'", pod_id, space_id))?;

    Ok(StatusCode::CREATED)
}


// Handler for DELETE /api/pods/:space_id/:pod_id
pub async fn delete_pod_from_space(
    State(pool): State<ConnectionPool>,
    Path((space_id, pod_id)): Path<(String, String)>,
) -> Result<impl IntoResponse, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;

    let space_id_clone = space_id.clone();
    let pod_id_clone = pod_id.clone();

    let rows_deleted = conn
        .interact(move |conn| {
            conn.execute(
                "DELETE FROM pods WHERE space = ?1 AND id = ?2",
                [space_id_clone, pod_id_clone],
            )
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("DB interaction failed for delete_pod_from_space")?
        .context(format!("Failed to delete pod '{}' from space '{}'", pod_id, space_id))?;

    if rows_deleted == 0 {
        Err(AppError::NotFound(format!(
            "Pod with id '{}' not found in space '{}'",
            pod_id, space_id
        )))
    } else {
        Ok(StatusCode::NO_CONTENT)
    }
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

    let space_clone = space.clone(); 
    let pods = conn
        .interact(move |conn|
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
        .await 
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("Database interaction failed")? 
        .context(format!("Failed to query pods for space '{}'", space))?; 

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

    let space_clone = space.clone(); 
    let id_clone = id.clone(); 

    let pod_info_result = conn
        .interact(move |conn| -> anyhow::Result<PodInfo> { 
            let mut stmt = conn.prepare(
                "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            let pod_info = stmt.query_row([&space_clone, &id_clone], |row| {
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
            });
            
            match pod_info {
                Ok(pod) => Ok(pod),
                Err(rusqlite::Error::QueryReturnedNoRows) => {
                    Err(anyhow::anyhow!(rusqlite::Error::QueryReturnedNoRows))
                }
                Err(e) => Err(anyhow::Error::from(e).context("Failed during pod query_row")), 
            }
        })
        .await 
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e)) 
        .context("Database interaction failed")?;
        
    match pod_info_result {
        Ok(pod) => Ok(Json(pod)),
        Err(err) => {
            if let Some(rusqlite_err) = err.downcast_ref::<rusqlite::Error>() {
                if matches!(rusqlite_err, rusqlite::Error::QueryReturnedNoRows) {
                    return Err(AppError::NotFound(format!(
                        "Pod with id '{}' not found in space '{}'",
                        id, space
                    )));
                }
            }
            Err(AppError::DatabaseError(err))
        }
    }
}

// Handler for POST /api/pods/sign
pub async fn sign_pod(
    Json(payload): Json<SignRequest>,
) -> Result<Json<SignedPod>, AppError> {
    log::debug!("Received sign request: {:?}", "payload hidden"); 

    let mut signer = MockSigner { pk: payload.private_key };
    log::debug!("Created signer for pk: {}", signer.pk);

    let params = crate::middleware::Params::default(); 
    let mut builder = SignedPodBuilder::new(&params);
    log::debug!("Created SignedPodBuilder");

    for (key, value) in payload.entries {
        log::trace!("Inserting entry: key='{}', value=...", key); 
        builder.insert(&key, value);
    }
    log::debug!("Inserted all entries into builder");

    let signed_pod = builder.sign(&mut signer)
        .context("Failed to sign the POD")?; 
    log::debug!("Successfully signed POD with id: {}", signed_pod.id().0);

    Ok(Json(signed_pod))
}

// Handler for POST /api/hash
pub async fn hash_string(body: String) -> Result<Json<Hash>, AppError> {
    log::debug!("Received hash request for string: {:?}", body);
    let hash_result = hash_str(&body);
    log::debug!("Computed hash: {}", hash_result);
    Ok(Json(hash_result))
}


#[cfg(test)]
mod tests {
    use axum_test::TestServer;
    use chrono::Utc;
    use rusqlite::params;
    use serde_json::json;

    use super::*; // Imports PodInfo, SignRequest etc. and handlers
    use crate::{middleware::Key, server::{db::{self, init_db_pool, ConnectionPool}, routes::create_router}};

    // Helper to insert a test space
    async fn insert_test_space(pool: &ConnectionPool, id: &str) {
        let conn = pool.get().await.unwrap();
        let id_owned = id.to_string();
        conn.interact(move |conn| {
            let now = Utc::now().to_rfc3339();
            conn.execute(
                "INSERT INTO spaces (id, created_at) VALUES (?1, ?2)",
                params![id_owned, now],
            )
        })
        .await
        .unwrap()
        .unwrap();
    }

    // Helper to insert a test pod
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
        let id_owned = id.to_string();
        let pod_type_owned = pod_type.to_string();
        let pod_class_owned = pod_class.to_string();
        let data_owned = data.clone();
        let label_owned = label.map(|s| s.to_string());
        let space_owned = space.to_string();

        conn.interact(move |conn| {
            let now = Utc::now().to_rfc3339();
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

    // Helper to deserialize response
    async fn response_to_pods(response: axum_test::TestResponse) -> Vec<PodInfo> {
        response.json()
    }
    
    // Test server setup specific to these tests
    pub async fn create_test_server_with_pool() -> (TestServer, ConnectionPool) {
        let pool = init_db_pool(None).await.expect("Failed to init db pool for test");
        db::create_schema(&pool).await.expect("Failed to create schema for test");
        let router = create_router(pool.clone());
        (TestServer::new(router).unwrap(), pool)
    }


    #[tokio::test]
    async fn test_list_pods_in_space() {
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_list_pods_in_space");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        // Create spaces before inserting pods
        insert_test_space(&pool, "space1").await;
        insert_test_space(&pool, "space2").await;

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

        let response = server.get("/api/pods/space2").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 1);
        assert_eq!(pods[0].id, "id3");
        assert_eq!(pods[0].pod_type, "main");
        assert_eq!(pods[0].label, Some("label3".to_string()));
        assert_eq!(pods[0].data, pod3_data);
        assert_eq!(pods[0].space, "space2");

        let response = server.get("/api/pods/nonexistent_space").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;
        assert!(pods.is_empty());
    }

    #[tokio::test]
    async fn test_get_pod_by_id_success() {
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_get_pod_by_id_success");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        let pod_data = json!({ "detail": "unique" });
        // Ensure the space exists before inserting the pod
        insert_test_space(&pool, "test_space").await;
        insert_test_pod(&pool, "test_id", "main", "mock", &pod_data, Some("test_label"), "test_space").await;

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
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_get_pod_by_id_not_found_in_space");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();
        
        let space_name = "other_space";
        // No, this test explicitly tests when the *pod* is not in the *requested* space, but the pod might be in *another* space.
        // So, we create 'other_space' and put the pod there.
        insert_test_space(&pool, space_name).await; 

        let pod_data = json!({});
        insert_test_pod(&pool, "test_id", "main", "mock", &pod_data, None, space_name).await;

        // Requesting from a different, non-existent space for this pod (or rather, a space where this pod isn't)
        // We also need to ensure "test_space" actually exists for the NOT_FOUND to be about the pod, not the space.
        insert_test_space(&pool, "test_space").await;

        let response = server.get("/api/pods/test_space/test_id").await; 
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains("Pod with id 'test_id' not found in space 'test_space'"));
    }

    #[tokio::test]
    async fn test_get_pod_by_id_not_found_id() {
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_get_pod_by_id_not_found_id");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        let space_name = "test_space";
        insert_test_space(&pool, space_name).await; // Ensure the space exists
        
        let pod_data = json!({});
        insert_test_pod(&pool, "other_id", "main", "mock", &pod_data, None, space_name).await;

        let response = server.get("/api/pods/test_space/non_existent_id").await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains("Pod with id 'non_existent_id' not found in space 'test_space'"));
    }

    #[tokio::test]
    async fn test_sign_pod_success() {
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_sign_pod_success");
        let router = create_router(pool.clone()); 
        let server = TestServer::new(router).unwrap();

        let request_payload = json!({
            "private_key": "my_secret_key",
            "entries": {
                "name": "Alice", 
                "age": {"Int": "30"}, 
                "city": "Metropolis",
                "verified": true, 
                "tags": ["a", "b", {"Int": "123"}] 
            }
        });

        let response = server.post("/api/pods/sign").json(&request_payload).await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let response_pod: SignedPod = response.json();

        assert!(response_pod.verify().is_ok());
        assert_eq!(response_pod.kvs().len(), 7); 
        assert!(response_pod.kvs().contains_key(&Key::from("name")));
        assert_eq!(response_pod.kvs().get(&Key::from("name")), Some(&PodValue::from("Alice")));
        assert_eq!(response_pod.kvs().get(&Key::from("age")), Some(&PodValue::from(30)));
    }

    #[tokio::test]
    async fn test_hash_string_success() {
        let pool = init_db_pool(None).await.expect("Failed to init db pool");
        db::create_schema(&pool).await.expect("Failed to create schema for test_hash_string_success");
        let router = create_router(pool.clone());
        let server = TestServer::new(router).unwrap();

        let input_string = "hello world";
        let response = server
            .post("/api/hash")
            .content_type("text/plain") 
            .text(input_string.to_string()) 
            .await;

        assert_eq!(response.status_code(), StatusCode::OK);
        let response_hash: Hash = response.json();
        let expected_hash = hash_str(input_string);
        assert_eq!(response_hash, expected_hash);
    }
    
    #[tokio::test]
    async fn test_import_pod_to_space_and_delete() {
        let (server, pool) = create_test_server_with_pool().await;
        let space_id = "pod-space-for-import-delete"; // Unique name
        let pod_id = "test-pod-import-delete";

        // Create space first
        insert_test_space(&pool, space_id).await;

        let import_payload = json!({
            "podType": "test-type-id",
            "podClass": "test-class-id",
            "data": { "key": "value" },
            "label": "My Test Pod For Import Delete"
        });
        let response = server.post(&format!("/api/pods/{}/{}", space_id, pod_id))
            .json(&import_payload)
            .await;
        assert_eq!(response.status_code(), StatusCode::CREATED, "Response: {:?}", response.text());

        let conn_check = pool.get().await.unwrap();
        let space_id_check = space_id.to_string();
        let pod_id_check = pod_id.to_string();
        let pod_info_res: Result<PodInfo, _> = conn_check.interact(move |conn_inner| {
             let mut stmt = conn_inner.prepare(
                "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            stmt.query_row([&space_id_check, &pod_id_check], |row| {
                let data_blob: Vec<u8> = row.get(3)?;
                let data_value: Value = serde_json::from_slice(&data_blob).unwrap();
                Ok(PodInfo {
                    id: row.get(0)?,
                    pod_type: row.get(1)?,
                    pod_class: row.get(2)?,
                    data: data_value,
                    label: row.get(4)?,
                    created_at: row.get(5)?,
                    space: row.get(6)?,
                })
            })
        }).await.unwrap();
        
        assert!(pod_info_res.is_ok(), "Pod not found in DB after import");
        let pod_info = pod_info_res.unwrap();
        assert_eq!(pod_info.id, pod_id);
        assert_eq!(pod_info.pod_type, "test-type-id");

        let response = server.delete(&format!("/api/pods/{}/{}", space_id, pod_id)).await;
        assert_eq!(response.status_code(), StatusCode::NO_CONTENT);

        let response = server.get(&format!("/api/pods/{}/{}", space_id, pod_id)).await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
    }
} 