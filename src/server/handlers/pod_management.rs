use anyhow::Context;
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use hex::ToHex;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use chrono::Utc;

use crate::frontend::{serialization::{MainPodHelper, SignedPodHelper}, MainPod};
use crate::{backends::plonky2::mock::signedpod::MockSigner, frontend::{SignedPod, SignedPodBuilder}, server::db::ConnectionPool};
use crate::middleware::{Hash, hash_str, Value as PodValue}; 

use super::AppError; 

#[derive(Serialize, Deserialize, JsonSchema, Debug, Clone, PartialEq)]
#[serde(tag = "pod_data_variant", content = "pod_data_payload")] // This will determine the JSON structure
pub enum PodData {
    Signed(SignedPodHelper),
    Main(MainPodHelper),
}

impl PodData {
    /// Returns a string representation of the pod data variant.
    pub fn type_str(&self) -> &'static str {
        match self {
            PodData::Signed(_) => "signed",
            PodData::Main(_) => "main",
        }
    }
}

#[derive(Serialize, Deserialize, JsonSchema)]
pub struct PodInfo {
    pub id: String,
    pub pod_type: String, // This will store the string "signed" or "main" from the DB
    pub pod_class: String,
    pub data: PodData,   // Changed from Value to the strongly-typed enum
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

// Handler for POST /api/pods/:space_id
pub async fn import_pod_to_space(
    State(pool): State<ConnectionPool>,
    Path(space_id): Path<String>,
    Json(payload): Json<ImportPodRequest>,
) -> Result<impl IntoResponse, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;
    
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

    // Re-bind pod_data_enum so it can be moved into PodInfo later
    let final_pod_data_enum = match payload.pod_type.as_str() {
        "signed" => {
            let helper: SignedPodHelper = serde_json::from_value(payload.data.clone())
                .context("Failed to deserialize data into SignedPodHelper for PodInfo construction")?;
            PodData::Signed(helper)
        }
        "main" => {
            let helper: MainPodHelper = serde_json::from_value(payload.data.clone())
                .context("Failed to deserialize data into MainPodHelper for PodInfo construction")?;
            PodData::Main(helper)
        }
        _ => unreachable!(), // Should have been caught earlier
    };

    let pod_id_obj = match &final_pod_data_enum  { // Borrow here
        PodData::Signed(signed_pod_helper) => SignedPod::try_from(signed_pod_helper.clone()).unwrap().id(), // Clone helper if needed by try_from
        PodData::Main(main_pod_helper) => MainPod::try_from(main_pod_helper.clone()).unwrap().id() // Clone helper if needed by try_from
    };
    
    // Serialize the Hash part of Id (pod_id_obj.0) to a string for DB and PodInfo
    let pod_id_string_for_db_and_info: String = pod_id_obj.encode_hex();
    
    let pod_id_for_response = pod_id_string_for_db_and_info.clone();
    let pod_id_for_error_msg = pod_id_string_for_db_and_info.clone();

    // The data_blob for DB storage must be from the original deserialization to ensure it matches what was validated.
    // For PodInfo, we use final_pod_data_enum which is a fresh deserialization (or could be the original pod_data_enum if we clone it before the first match).
    // To be safe and avoid complex cloning, let's re-serialize the validated `final_pod_data_enum` for the database.
    let data_blob_for_db = serde_json::to_vec(&final_pod_data_enum)
        .context("Failed to serialize final PodData enum to JSON for storage")?;

    let space_id_clone_for_db = space_id.clone();
    let pod_type_for_db_and_info = payload.pod_type.clone(); 
    let pod_class_for_db_and_info = payload.pod_class.clone();
    let label_for_db_and_info = payload.label.clone();
    let created_at_for_info = now.clone(); // For PodInfo response

    conn.interact(move |conn| {
        conn.execute(
            "INSERT INTO pods (id, pod_type, pod_class, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            rusqlite::params![
                pod_id_string_for_db_and_info, // Use the serialized string ID
                pod_type_for_db_and_info, 
                pod_class_for_db_and_info, 
                data_blob_for_db, // Use the blob from final_pod_data_enum
                label_for_db_and_info, 
                now, // For DB
                space_id_clone_for_db
            ],
        )
    })
    .await
    .map_err(|e| anyhow::anyhow!("InteractError: {}", e)) 
    .context("DB interaction failed for import_pod_to_space")?
    .context(format!("Failed to import pod '{}' into space '{}'", pod_id_for_error_msg, space_id))?;

    // Construct PodInfo for the response
    let created_pod_info = PodInfo {
        id: pod_id_for_response, // Use the cloned string ID for PodInfo
        pod_type: payload.pod_type.clone(),
        pod_class: payload.pod_class.clone(),
        data: final_pod_data_enum, // Use the enum instance we created for ID generation
        label: payload.label.clone(),
        created_at: created_at_for_info,
        space: space_id.clone(),
    };

    Ok((StatusCode::CREATED, Json(created_pod_info)))
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
                    let id_val: String = row.get(0)?;
                    let pod_type_from_db: String = row.get(1)?;
                    let pod_class_val: String = row.get(2)?;
                    let data_blob: Vec<u8> = row.get(3)?;
                    let label_val: Option<String> = row.get(4)?;
                    let created_at_val: String = row.get(5)?;
                    let space_val: String = row.get(6)?;

                    let pod_data_enum: PodData = serde_json::from_slice(&data_blob).map_err(|e| {
                        log::error!("Failed to deserialize PodData for pod id '{}' in space '{}': {:?}. Data blob (first 100 bytes): {:?}", 
                                    id_val, space_clone, e, data_blob.iter().take(100).collect::<Vec<_>>());
                        rusqlite::Error::FromSqlConversionFailure(
                            3, // Column index
                            rusqlite::types::Type::Blob,
                            Box::new(e),
                        )
                    })?;

                    // Consistency check
                    if pod_type_from_db != pod_data_enum.type_str() {
                        log::warn!(
                            "Data inconsistency for pod_id '{}' in space '{}': DB pod_type is '{}' but deserialized PodData is for '{}'.",
                            id_val, space_clone, pod_type_from_db, pod_data_enum.type_str()
                        );
                        // Depending on strictness, you might choose to return an error here.
                        // For now, we'll log a warning and proceed, using the DB pod_type for PodInfo.
                    }

                    Ok(PodInfo {
                        id: id_val,
                        pod_type: pod_type_from_db, // Use the string from the 'pod_type' column
                        pod_class: pod_class_val,
                        data: pod_data_enum,
                        label: label_val,
                        created_at: created_at_val,
                        space: space_val,
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
        .interact(move |conn| -> anyhow::Result<PodInfo> { // Changed return type for interact
            let mut stmt = conn.prepare(
                "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            let pod_info_internal = stmt.query_row([&space_clone, &id_clone], |row| {
                let id_val: String = row.get(0)?;
                let pod_type_from_db: String = row.get(1)?;
                let pod_class_val: String = row.get(2)?;
                let data_blob: Vec<u8> = row.get(3)?;
                let label_val: Option<String> = row.get(4)?;
                let created_at_val: String = row.get(5)?;
                let space_val: String = row.get(6)?;

                let pod_data_enum: PodData = serde_json::from_slice(&data_blob).map_err(|e| {
                    log::error!("Failed to deserialize PodData for pod id '{}' in space '{}': {:?}. Data blob (first 100 bytes): {:?}", 
                                id_val, space_clone, e, data_blob.iter().take(100).collect::<Vec<_>>());
                    rusqlite::Error::FromSqlConversionFailure(
                        3, 
                        rusqlite::types::Type::Blob,
                        Box::new(e),
                    )
                })?;

                // Consistency check
                if pod_type_from_db != pod_data_enum.type_str() {
                    log::warn!(
                        "Data inconsistency for pod_id '{}' in space '{}': DB pod_type is '{}' but deserialized PodData is for '{}'.",
                        id_val, space_clone, pod_type_from_db, pod_data_enum.type_str()
                    );
                    // Depending on strictness, you might choose to return an error here.
                }

                Ok(PodInfo {
                    id: id_val,
                    pod_type: pod_type_from_db,
                    pod_class: pod_class_val,
                    data: pod_data_enum,
                    label: label_val,
                    created_at: created_at_val,
                    space: space_val,
                })
            });
            
            match pod_info_internal {
                Ok(pod) => Ok(pod),
                Err(rusqlite::Error::QueryReturnedNoRows) => {
                    // Specific error to be handled by the outer match
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
            // Check if the error is specifically QueryReturnedNoRows from the interact block
            if err.downcast_ref::<rusqlite::Error>().map_or(false, |e| matches!(e, rusqlite::Error::QueryReturnedNoRows)) {
                 Err(AppError::NotFound(format!(
                    "Pod with id '{}' not found in space '{}'",
                    id, space
                )))
            } else {
                // For other errors, wrap them in AppError::DatabaseError
                Err(AppError::DatabaseError(err.context(format!(
                    "Failed to get pod '{}' from space '{}'",
                    id, space
                ))))
            }
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
    use std::collections::HashMap;

    use axum_test::TestServer;
    use chrono::Utc;
    use hex::ToHex;
    use rusqlite::params;
    use serde_json::{json, Value};

    use super::*; // Imports PodInfo, SignRequest etc. and handlers
    use crate::{middleware::{self, Key}, server::{db::{self, init_db_pool, ConnectionPool}, routes::create_router}};

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
        pod_type: &str, // Should be "main" or "signed"
        pod_class: &str,
        data_payload: &Value, // For "main", this is the full MainPodHelper. For "signed", this is the 'entries' map.
        label: Option<&str>,
        space: &str,
    ) {
        let conn = pool.get().await.unwrap();
        let id_owned = id.to_string();
        let pod_type_owned = pod_type.to_string();
        let pod_class_owned = pod_class.to_string();
        let label_owned = label.map(|s| s.to_string());
        let space_owned = space.to_string();

        let pod_data_enum_for_test = match pod_type {
            "signed" => {
                // For "signed" pods in tests, data_payload represents the 'entries'
                let entries_map: HashMap<Key, PodValue> = serde_json::from_value(data_payload.clone())
                    .expect("Test data_payload for SignedPodHelper entries failed to deserialize to HashMap<Key, PodValue>");
                let helper = SignedPodHelper {
                    entries: entries_map,
                    proof: "default_test_signed_proof".to_string(),
                    pod_class: "Signed".to_string(), // Must match what SignedPod::try_from expects
                    pod_type: "Mock".to_string(),    // Must match
                };
                PodData::Signed(helper)
            }
            "main" => {
                // For "main" pods, data_payload is the full MainPodHelper structure
                let helper: MainPodHelper = serde_json::from_value(data_payload.clone())
                    .expect("Test data failed to deserialize to MainPodHelper");
                PodData::Main(helper)
            }
            _ => panic!("Unsupported pod_type '{}' in test setup. Must be \"main\" or \"signed\".", pod_type),
        };

        conn.interact(move |conn| {
            let now = Utc::now().to_rfc3339();
            let data_blob = serde_json::to_vec(&pod_data_enum_for_test).unwrap(); 
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

        // Define standard payloads for helpers
        let main_pod_helper_payload = json!({
            "publicStatements": [],
            "proof": "test_proof_main_1",
            "podClass": "Main",
            "podType": "Mock"
        });
        let signed_pod_helper_entries_payload = json!({ "value_signed": { "Int": "2" } });
        // Note: insert_test_pod for "signed" wraps these entries into a full SignedPodHelper.

        let main_pod_helper_payload3 = json!({
            "publicStatements": [],
            "proof": "test_proof_main_3",
            "podClass": "Main",
            "podType": "Mock"
        });

        insert_test_pod(
            &pool,
            "id1",
            "main",
            "mock_class_main", // pod_class for the DB
            &main_pod_helper_payload,
            Some("label1"),
            "space1",
        )
        .await;
        insert_test_pod(
            &pool, 
            "id2", 
            "signed", 
            "mock_class_signed", // pod_class for the DB
            &signed_pod_helper_entries_payload, 
            None, 
            "space1"
        ).await;
        insert_test_pod(
            &pool,
            "id3",
            "main",
            "mock_class_main", // pod_class for the DB
            &main_pod_helper_payload3,
            Some("label3"),
            "space2",
        )
        .await;

        let response = server.get("/api/pods/space1").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 2);
        
        let expected_main_helper1: MainPodHelper = serde_json::from_value(main_pod_helper_payload.clone()).unwrap();
        let expected_pod_data1 = PodData::Main(expected_main_helper1);
        assert!(pods.iter().any(|p| p.id == "id1"
            && p.pod_type == "main"
            && p.pod_class == "mock_class_main"
            && p.label == Some("label1".to_string())
            && p.data == expected_pod_data1
            && p.space == "space1"));

        // Construct the expected SignedPodHelper by deserializing a canonical JSON representation
        let full_expected_signed_helper2_json = json!({
            "entries": signed_pod_helper_entries_payload.clone(), // The entries provided to insert_test_pod
            "proof": "default_test_signed_proof", // Matches the default proof in insert_test_pod
            "podClass": "Signed",               // Matches the default podClass in insert_test_pod
            "podType": "Mock"                   // Matches the default podType in insert_test_pod
        });
        let expected_signed_helper2: SignedPodHelper = serde_json::from_value(full_expected_signed_helper2_json).unwrap();
        let expected_pod_data2 = PodData::Signed(expected_signed_helper2);

        assert!(pods.iter().any(|p| p.id == "id2"
            && p.pod_type == "signed"
            && p.pod_class == "mock_class_signed"
            && p.label.is_none()
            && p.data == expected_pod_data2
            && p.space == "space1"));
        assert!(pods[0].created_at.contains('T'));

        let response = server.get("/api/pods/space2").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 1);
        assert_eq!(pods[0].id, "id3");
        assert_eq!(pods[0].pod_type, "main");
        assert_eq!(pods[0].pod_class, "mock_class_main");
        assert_eq!(pods[0].label, Some("label3".to_string()));
        let expected_main_helper3: MainPodHelper = serde_json::from_value(main_pod_helper_payload3.clone()).unwrap();
        let expected_pod_data3 = PodData::Main(expected_main_helper3);
        assert_eq!(pods[0].data, expected_pod_data3);
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

        let main_pod_payload_for_get = json!({
            "publicStatements": [],
            "proof": "test_get_unique_proof",
            "podClass": "Main",
            "podType": "Mock"
        });
        insert_test_space(&pool, "test_space").await;
        insert_test_pod(
            &pool, 
            "test_id", 
            "main", 
            "mock_get_class", 
            &main_pod_payload_for_get, 
            Some("test_label"), 
            "test_space"
        ).await;

        let response = server.get("/api/pods/test_space/test_id").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pod: PodInfo = response.json();

        assert_eq!(pod.id, "test_id");
        assert_eq!(pod.pod_type, "main");
        assert_eq!(pod.pod_class, "mock_get_class");
        let expected_helper_get: MainPodHelper = serde_json::from_value(main_pod_payload_for_get.clone()).unwrap();
        let expected_pod_data_get = PodData::Main(expected_helper_get);
        assert_eq!(pod.data, expected_pod_data_get);
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

        let main_pod_payload_other_space = json!({
            "publicStatements": [],
            "proof": "other_space_proof",
            "podClass": "Main",
            "podType": "Mock"
        });
        insert_test_pod(
            &pool, 
            "test_id", 
            "main", 
            "mock_class_other", 
            &main_pod_payload_other_space, 
            None, 
            space_name // Pod is in 'other_space'
        ).await;

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
        
        let main_pod_payload_other_id = json!({
            "publicStatements": [],
            "proof": "other_id_proof",
            "podClass": "Main",
            "podType": "Mock"
        });
        insert_test_pod(
            &pool, 
            "other_id", 
            "main", 
            "mock_class_other_id", 
            &main_pod_payload_other_id, 
            None, 
            space_name
        ).await;

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

        // Create space first
        insert_test_space(&pool, space_id).await;

        let mut signer = MockSigner {
          pk: "0x1234567890abcdef".to_string(),
        };
        let params = middleware::Params::default();
        let mut pod_builder = SignedPodBuilder::new(&params);
        pod_builder.insert("test", "test");
        let pod = pod_builder.sign(&mut signer).unwrap();
        let pod_id = pod.id();
        let pod_id_string: String = pod_id.encode_hex();
        let import_payload = json!({
            "podType": "signed",
            "podClass": "mock",
            "data": serde_json::to_value(pod).unwrap(),
            "label": "My Test Pod For Import Delete"
        });
        
        let response = server.post(&format!("/api/pods/{}", space_id))
            .json(&import_payload)
            .await;
        println!("Response: {:?}", response.text());
        assert_eq!(response.status_code(), StatusCode::CREATED, "Response: {:?}", response.text());

        let conn_check = pool.get().await.unwrap();
        let space_id_check = space_id.to_string();
        let pod_id_check = pod_id_string.clone();
        let pod_info_res: Result<PodInfo, _> = conn_check.interact(move |conn_inner| {
             let mut stmt = conn_inner.prepare(
                "SELECT id, pod_type, pod_class, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            stmt.query_row([&space_id_check, &pod_id_check.clone()], |row| {
                let id_val: String = row.get(0)?;
                let pod_type_from_db: String = row.get(1)?;
                let pod_class_val: String = row.get(2)?;
                let data_blob: Vec<u8> = row.get(3)?;
                let pod_data_from_db: PodData = serde_json::from_slice(&data_blob).unwrap_or_else(|e| 
                    panic!("Failed to deserialize PodData from DB in test: {:?}. Blob: {:?}", e, data_blob)
                );
                let label_val: Option<String> = row.get(4)?;
                let created_at_val: String = row.get(5)?;
                let space_val: String = row.get(6)?;
                Ok(PodInfo {
                    id: id_val,
                    pod_type: pod_type_from_db,
                    pod_class: pod_class_val,
                    data: pod_data_from_db,
                    label: label_val,
                    created_at: created_at_val,
                    space: space_val,
                })
            })
        }).await.unwrap();
        
        assert!(pod_info_res.is_ok(), "Pod not found in DB after import: {:?}", pod_info_res.err());
        let pod_info = pod_info_res.unwrap();
        assert_eq!(pod_info.id, pod_id_string);
        assert_eq!(pod_info.pod_type, "signed"); 
        assert_eq!(pod_info.pod_class, "mock"); // Check against the DB class

        // Assert data content
        // let expected_imported_helper: MainPodHelper = serde_json::from_value(import_main_pod_helper_data.clone()).unwrap();
        // let expected_pod_data_imported = PodData::Main(expected_imported_helper);
        // assert_eq!(pod_info.data, expected_pod_data_imported);

        let response = server.delete(&format!("/api/pods/{}/{}", space_id, pod_id_string)).await;
        assert_eq!(response.status_code(), StatusCode::NO_CONTENT);

        let response = server.get(&format!("/api/pods/{}/{}", space_id, pod_id)).await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
    }
} 