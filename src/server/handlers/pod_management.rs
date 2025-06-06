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

use crate::{
    backends::plonky2::mock::signedpod::MockSigner,
    frontend::{serialization::{SerializedMainPod, SerializedSignedPod}, MainPod, SignedPod, SignedPodBuilder},
    middleware::{hash_str, Hash, Value as PodValue},
    server::db::ConnectionPool,
};

use super::AppError; 

#[derive(Serialize, Deserialize, JsonSchema, Debug, Clone, PartialEq)]
#[serde(tag = "pod_data_variant", content = "pod_data_payload")] // This will determine the JSON structure
pub enum PodData {
    Signed(SerializedSignedPod),
    Main(SerializedMainPod),
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
            let helper: SerializedSignedPod = serde_json::from_value(payload.data.clone())
                .context("Failed to deserialize data into SerializedSignedPod for PodInfo construction")?;
            PodData::Signed(helper)
        }
        "main" => {
            let helper: SerializedMainPod = serde_json::from_value(payload.data.clone())
                .context("Failed to deserialize data into SerializedMainPod for PodInfo construction")?;
            PodData::Main(helper)
        }
        _ => unreachable!(), // Should have been caught earlier
    };

    let pod_id_obj = match &final_pod_data_enum  { // Borrow here
        PodData::Signed(signed_pod_helper) => SignedPod::from(signed_pod_helper.clone()).id(), // Clone helper if needed by try_from
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
    let label_for_db_and_info = payload.label.clone();
    let created_at_for_info = now.clone(); // For PodInfo response

    conn.interact(move |conn| {
        conn.execute(
            "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
            rusqlite::params![
                pod_id_string_for_db_and_info, // Use the serialized string ID
                pod_type_for_db_and_info, 
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
                    "SELECT id, pod_type, data, label, created_at, space FROM pods WHERE space = ?1",
                )?;
                let pod_iter = stmt.query_map([&space_clone], |row| {
                    let id_val: String = row.get(0)?;
                    let pod_type_from_db: String = row.get(1)?;
                    let data_blob: Vec<u8> = row.get(2)?;
                    let label_val: Option<String> = row.get(3)?;
                    let created_at_val: String = row.get(4)?;
                    let space_val: String = row.get(5)?;

                    let pod_data_enum: PodData = serde_json::from_slice(&data_blob).map_err(|e| {
                        log::error!("Failed to deserialize PodData for pod id '{}' in space '{}': {:?}. Data blob (first 100 bytes): {:?}", 
                                    id_val, space_clone, e, data_blob.iter().take(100).collect::<Vec<_>>());
                        rusqlite::Error::FromSqlConversionFailure(
                            2, // Column index updated
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
                "SELECT id, pod_type, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            let pod_info_internal = stmt.query_row([&space_clone, &id_clone], |row| {
                let id_val: String = row.get(0)?;
                let pod_type_from_db: String = row.get(1)?;
                let data_blob: Vec<u8> = row.get(2)?;
                let label_val: Option<String> = row.get(3)?;
                let created_at_val: String = row.get(4)?;
                let space_val: String = row.get(5)?;

                let pod_data_enum: PodData = serde_json::from_slice(&data_blob).map_err(|e| {
                    log::error!("Failed to deserialize PodData for pod id '{}' in space '{}': {:?}. Data blob (first 100 bytes): {:?}", 
                                id_val, space_clone, e, data_blob.iter().take(100).collect::<Vec<_>>());
                    rusqlite::Error::FromSqlConversionFailure(
                        2, // Column index updated
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
            if err.downcast_ref::<rusqlite::Error>().is_some_and(|e| matches!(e, rusqlite::Error::QueryReturnedNoRows)) {
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
    use axum_test::TestServer;
    use chrono::Utc;
    use hex::ToHex;
    use rusqlite::params;
    use serde_json::{json, Value};

    use super::*; // Imports PodInfo, SignRequest etc. and handlers
    use crate::{
        backends::plonky2::mock::{mainpod::MockProver, signedpod::MockSigner}, frontend::{MainPodBuilder, SignedPod, SignedPodBuilder}, middleware::{self, hash_str, Key, Params as PodParams, PodId, Value as PodValue}, op, server::{
            db::{self, init_db_pool, ConnectionPool},
            routes::create_router,
        } // Added MockProver
    };

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

    // Helper to insert a test pod (contract for data_payload changes)
    async fn insert_test_pod(
        pool: &ConnectionPool,
        id: &str, // This MUST be the hex string of the PodId embedded in data_payload
        pod_type: &str, // Should be "main" or "signed"
        data_payload: &Value, // MUST be a valid SerializedSignedPod or SerializedMainPod as JSON
        label: Option<&str>,
        space: &str,
    ) {
        let conn = pool.get().await.unwrap();
        let id_owned = id.to_string();
        let pod_type_owned = pod_type.to_string();
        let label_owned = label.map(|s| s.to_string());
        let space_owned = space.to_string();

        let pod_data_enum_for_test = match pod_type {
            "signed" => {
                let helper = serde_json::from_value(data_payload.clone())
                    .expect("Test data failed to deserialize to SerializedSignedPod");
                PodData::Signed(helper)
            }
            "main" => {
                // For "main" pods, data_payload is the full MainPodHelper structure
                let helper: SerializedMainPod = serde_json::from_value(data_payload.clone())
                    .expect("Test data failed to deserialize to SerializedMainPod");
                PodData::Main(helper)
            }
            _ => panic!("Unsupported pod_type '{}' in test setup. Must be \"main\" or \"signed\".", pod_type),
        };

        conn.interact(move |conn| {
            let now = Utc::now().to_rfc3339();
            let data_blob = serde_json::to_vec(&pod_data_enum_for_test).unwrap(); 
            conn.execute(
                "INSERT INTO pods (id, pod_type, data, label, created_at, space) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                params![id_owned, pod_type_owned, data_blob, label_owned, now, space_owned],
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

    // Helper function to create sample SerializedSignedPod data as serde_json::Value
    fn create_sample_signed_pod_data(params: &PodParams, unique_id_str: &str, entries: Vec<(&str, PodValue)>) -> (String, Value) {
        let mut signed_builder = SignedPodBuilder::new(params);
        for (key, value) in entries {
            signed_builder.insert(key, value);
        }
        // Use part of unique_id_str for signer to ensure some variation if needed, though id() is content-based
        let mut signer = MockSigner { pk: format!("test_signer_{}", unique_id_str) };
        let signed_pod = signed_builder.sign(&mut signer).expect("Failed to sign sample pod");
        
        let pod_id_str = signed_pod.id().encode_hex();
        let data_payload_value = serde_json::to_value(&signed_pod).expect("Failed to serialize SignedPod for sample data");
        (pod_id_str, data_payload_value)
    }

    // Helper function to create sample SerializedMainPod data as serde_json::Value
    fn create_sample_main_pod_data(params: &PodParams) -> (String, Value) {
        let mut main_builder = MainPodBuilder::new(params);
        // Add a simple operation: new_entry
        main_builder.priv_op(op!(new_entry, ("test", middleware::Value::from("sample_value"))))
            .expect("Failed to add new_entry op to sample main pod builder");

        let mut prover = MockProver {};
        let main_pod = main_builder.prove(&mut prover, params).expect("Failed to prove sample main pod");

        let pod_id_str = main_pod.id().encode_hex();
        let data_payload_value = serde_json::to_value(&main_pod).expect("Failed to serialize MainPod for sample data");
        (pod_id_str, data_payload_value)
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

        let test_params = PodParams::default();

        // Create and insert a MainPod using helper
        let (main_pod1_id_str, main_pod1_data_payload) = create_sample_main_pod_data(&test_params);
        insert_test_pod(
            &pool,
            &main_pod1_id_str,
            "main",
            &main_pod1_data_payload,
            Some("label1"),
            "space1",
        )
        .await;

        // Create and insert a SignedPod using helper
        let (signed_pod1_id_str, signed_pod1_data_payload) = create_sample_signed_pod_data(
            &test_params, 
            "list_signed1", 
            vec![("value_signed", PodValue::from(2))]
        );
        insert_test_pod(
            &pool,
            &signed_pod1_id_str,
            "signed",
            &signed_pod1_data_payload,
            None,
            "space1",
        )
        .await;

        // Create and insert another MainPod for space2 using helper
        let (main_pod2_id_str, main_pod2_data_payload) = create_sample_main_pod_data(&test_params);
        insert_test_pod(
            &pool,
            &main_pod2_id_str,
            "main",
            &main_pod2_data_payload,
            Some("label3"),
            "space2",
        )
        .await;

        let response = server.get("/api/pods/space1").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pods = response_to_pods(response).await;

        assert_eq!(pods.len(), 2);
        
        let expected_serialized_main_pod1: SerializedMainPod = serde_json::from_value(main_pod1_data_payload.clone()).unwrap();
        let expected_pod_data1 = PodData::Main(expected_serialized_main_pod1);
        assert!(pods.iter().any(|p| p.id == main_pod1_id_str
            && p.pod_type == "main"
            && p.data == expected_pod_data1
            && p.label == Some("label1".to_string())
            && p.space == "space1"));

        let expected_serialized_signed_pod1: SerializedSignedPod = serde_json::from_value(signed_pod1_data_payload.clone()).unwrap();
        let expected_pod_data2 = PodData::Signed(expected_serialized_signed_pod1);
        assert!(pods.iter().any(|p| p.id == signed_pod1_id_str
            && p.pod_type == "signed"
            && p.data == expected_pod_data2
            && p.space == "space1"));

        let response_space2 = server.get("/api/pods/space2").await;
        assert_eq!(response_space2.status_code(), StatusCode::OK);
        let pods_space2 = response_to_pods(response_space2).await;

        assert_eq!(pods_space2.len(), 1);
        let p2 = &pods_space2[0];
        assert_eq!(p2.id, main_pod2_id_str);
        assert_eq!(p2.pod_type, "main");
        let expected_serialized_main_pod2: SerializedMainPod = serde_json::from_value(main_pod2_data_payload.clone()).unwrap();
        assert_eq!(p2.data, PodData::Main(expected_serialized_main_pod2));
        assert_eq!(p2.label, Some("label3".to_string()));
    }

    #[tokio::test]
    async fn test_get_pod_by_id_success() {
        let (server, pool) = create_test_server_with_pool().await;
        let space_name = "get_test_space";
        insert_test_space(&pool, space_name).await;

        let test_params = PodParams::default();
        let (main_pod_id_str_for_get, main_pod_data_payload_for_get) = 
            create_sample_main_pod_data(&test_params);

        // Fetch created_at after insertion for reliable comparison
        insert_test_pod(
            &pool,
            &main_pod_id_str_for_get,
            "main",
            &main_pod_data_payload_for_get,
            Some("test_label_get"),
            space_name,
        )
        .await;
        
        let response = server.get(&format!("/api/pods/{}/{}", space_name, main_pod_id_str_for_get)).await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let pod: PodInfo = response.json();

        assert_eq!(pod.id, main_pod_id_str_for_get);
        assert_eq!(pod.pod_type, "main");
        assert_eq!(pod.space, space_name);
        let expected_serialized_main_pod: SerializedMainPod = serde_json::from_value(main_pod_data_payload_for_get.clone()).unwrap();
        assert_eq!(pod.data, PodData::Main(expected_serialized_main_pod));
        assert_eq!(pod.label, Some("test_label_get".to_string()));
    }

    #[tokio::test]
    async fn test_get_pod_by_id_not_found_in_space() {
        let (server, pool) = create_test_server_with_pool().await;
        
        let space_name_correct = "other_space_for_pod";
        let space_name_request = "test_space_for_request";

        insert_test_space(&pool, space_name_correct).await;
        insert_test_space(&pool, space_name_request).await; // Ensure requesting space exists

        let test_params = PodParams::default();
        let (pod_id_str, pod_data) = create_sample_main_pod_data(&test_params);
        
        insert_test_pod(
            &pool, 
            &pod_id_str, 
            "main", 
            &pod_data, 
            None, 
            space_name_correct // Pod is in 'other_space_for_pod'
        ).await;

        let response = server.get(&format!("/api/pods/{}/{}", space_name_request, pod_id_str)).await; 
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains(format!("Pod with id '{}' not found in space '{}'", pod_id_str, space_name_request).as_str()));
    }

    #[tokio::test]
    async fn test_get_pod_by_id_not_found_id() {
        let (server, pool) = create_test_server_with_pool().await;
        let space_name = "test_space_for_id_not_found";
        insert_test_space(&pool, space_name).await;
        
        let test_params = PodParams::default();
        let (existing_pod_id_str, existing_pod_data) = 
            create_sample_main_pod_data(&test_params);
        
        insert_test_pod(
            &pool, 
            &existing_pod_id_str, 
            "main", 
            &existing_pod_data, 
            None, 
            space_name
        ).await;

        let non_existent_id_str: String = PodId(hash_str("non_existent_pod_id_string_for_test")).encode_hex(); // Create a plausible but non-existent ID
        let response = server.get(&format!("/api/pods/{}/{}", space_name, non_existent_id_str)).await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
        let body = response.text();
        assert!(body.contains(format!("Pod with id '{}' not found in space '{}'", non_existent_id_str, space_name).as_str()));
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
                "SELECT id, pod_type, data, label, created_at, space FROM pods WHERE space = ?1 AND id = ?2",
            )?;
            stmt.query_row([&space_id_check, &pod_id_check.clone()], |row| {
                let id_val: String = row.get(0)?;
                let pod_type_from_db: String = row.get(1)?;
                let data_blob: Vec<u8> = row.get(2)?;
                let pod_data_from_db: PodData = serde_json::from_slice(&data_blob).unwrap_or_else(|e| 
                    panic!("Failed to deserialize PodData from DB in test: {:?}. Blob: {:?}", e, data_blob)
                );
                let label_val: Option<String> = row.get(3)?;
                let created_at_val: String = row.get(4)?;
                let space_val: String = row.get(5)?;
                Ok(PodInfo {
                    id: id_val,
                    pod_type: pod_type_from_db,
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