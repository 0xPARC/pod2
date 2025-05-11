use anyhow::Context;
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use chrono::Utc;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use super::AppError;
use crate::server::db::ConnectionPool;

#[derive(Serialize, Deserialize, JsonSchema)]
pub struct SpaceInfo {
    id: String,
    created_at: String,
}

#[derive(Deserialize)]
pub struct CreateSpaceRequest {
    id: String,
}

// --- Space Management Handlers ---

// Handler for GET /api/spaces
pub async fn list_spaces(
    State(pool): State<ConnectionPool>,
) -> Result<Json<Vec<SpaceInfo>>, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;
    let spaces = conn
        .interact(|conn| {
            let mut stmt = conn.prepare("SELECT id, created_at FROM spaces")?;
            let space_iter = stmt.query_map([], |row| {
                Ok(SpaceInfo {
                    id: row.get(0)?,
                    created_at: row.get(1)?,
                })
            })?;
            space_iter.collect::<Result<Vec<_>, _>>()
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("DB interaction failed for list_spaces")?
        .context("Failed to query spaces")?;
    Ok(Json(spaces))
}

// Handler for POST /api/spaces
pub async fn create_space(
    State(pool): State<ConnectionPool>,
    Json(payload): Json<CreateSpaceRequest>,
) -> Result<impl IntoResponse, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;
    let space_id = payload.id;
    let now = Utc::now().to_rfc3339();

    let space_id_clone = space_id.clone();
    conn.interact(move |conn| {
        conn.execute(
            "INSERT INTO spaces (id, created_at) VALUES (?1, ?2)",
            rusqlite::params![space_id_clone, now],
        )
    })
    .await
    .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
    .context("DB interaction failed for create_space")?
    .context(format!("Failed to create space '{}'", space_id))?;

    Ok(StatusCode::CREATED)
}

// Handler for DELETE /api/spaces/:space_id
pub async fn delete_space(
    State(pool): State<ConnectionPool>,
    Path(space_id): Path<String>,
) -> Result<impl IntoResponse, AppError> {
    let conn = pool.get().await.context("Failed to get DB connection")?;

    let space_id_clone_for_pods = space_id.clone();
    let _ = conn
        .interact(move |conn_inner| {
            conn_inner.execute(
                "DELETE FROM pods WHERE space = ?1",
                [&space_id_clone_for_pods],
            )
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError deleting pods: {}", e))
        .context(format!("Failed to delete pods for space '{}'", space_id))?;

    let space_id_clone_for_space = space_id.clone();
    let rows_deleted_space = conn
        .interact(move |conn_inner| {
            conn_inner.execute(
                "DELETE FROM spaces WHERE id = ?1",
                [&space_id_clone_for_space],
            )
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError deleting space: {}", e))
        .context("DB interaction failed for delete_space")?
        .context(format!("Failed to delete space '{}'", space_id))?;

    if rows_deleted_space == 0 {
        Err(AppError::NotFound(format!(
            "Space with id '{}' not found",
            space_id
        )))
    } else {
        Ok(StatusCode::NO_CONTENT)
    }
}

#[cfg(test)]
mod tests {
    // Renamed from space_management_tests to just tests for consistency
    use axum_test::TestServer;
    use rusqlite::OptionalExtension;
    use serde_json::json;

    use super::*;
    use crate::server::{
        db::{self, init_db_pool, ConnectionPool},
        routes::create_router,
    };

    // Test helper to create a server
    pub async fn create_test_server() -> TestServer {
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init db pool for test");
        db::create_schema(&pool)
            .await
            .expect("Failed to create schema in create_test_server");
        let router = create_router(pool.clone());
        TestServer::new(router).unwrap()
    }

    // Test helper to create a server and return the pool (useful for direct DB assertions)
    pub async fn create_test_server_with_pool() -> (TestServer, ConnectionPool) {
        let pool = init_db_pool(None)
            .await
            .expect("Failed to init db pool for test");
        db::create_schema(&pool)
            .await
            .expect("Failed to create schema in create_test_server_with_pool");
        let router = create_router(pool.clone());
        (TestServer::new(router).unwrap(), pool)
    }

    #[tokio::test]
    async fn test_create_list_delete_space() {
        let server = create_test_server().await;

        let response = server.get("/api/spaces").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let spaces: Vec<SpaceInfo> = response.json();
        assert!(spaces.is_empty());

        let space_id = "my-test-space";
        let response = server
            .post("/api/spaces")
            .json(&json!({"id": space_id}))
            .await;
        assert_eq!(response.status_code(), StatusCode::CREATED);

        let response = server.get("/api/spaces").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let spaces: Vec<SpaceInfo> = response.json();
        assert_eq!(spaces.len(), 1);
        assert_eq!(spaces[0].id, space_id);
        assert!(!spaces[0].created_at.is_empty());

        let response = server
            .post("/api/spaces")
            .json(&json!({"id": space_id}))
            .await;
        assert_ne!(response.status_code(), StatusCode::CREATED);
        assert_eq!(response.status_code(), StatusCode::INTERNAL_SERVER_ERROR);

        let response = server.delete(&format!("/api/spaces/{}", space_id)).await;
        assert_eq!(response.status_code(), StatusCode::NO_CONTENT);

        let response = server.get("/api/spaces").await;
        assert_eq!(response.status_code(), StatusCode::OK);
        let spaces: Vec<SpaceInfo> = response.json();
        assert!(spaces.is_empty());

        let response = server.delete("/api/spaces/non-existent-space").await;
        assert_eq!(response.status_code(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn test_delete_space_cascades_pods() {
        let (server, pool) = create_test_server_with_pool().await;
        let space_id1 = "cascade-space-1";
        let pod_id1 = "pod1"; // Not directly used for API calls here, but for context
        let space_id2 = "cascade-space-2";
        let pod_id2 = "pod2"; // Not directly used for API calls here

        assert_eq!(
            server
                .post("/api/spaces")
                .json(&json!({"id": space_id1}))
                .await
                .status_code(),
            StatusCode::CREATED
        );
        assert_eq!(
            server
                .post("/api/spaces")
                .json(&json!({"id": space_id2}))
                .await
                .status_code(),
            StatusCode::CREATED
        );

        // To test cascade, we need to import some pods. We'll use direct DB interaction for simplicity here,
        // assuming pod import functionality itself is tested elsewhere (e.g. pod_management.rs tests)
        let conn_setup = pool.get().await.unwrap();
        let s1_c = space_id1.to_string();
        let p_data_blob = serde_json::to_vec(&json!({})).unwrap();
        let now_str = Utc::now().to_rfc3339();
        conn_setup.interact(move |conn| {
            conn.execute("INSERT INTO pods (id, pod_type, pod_class, data, created_at, space) VALUES (?1, 't', 'c', ?2, ?3, ?4)", 
                         rusqlite::params![pod_id1, p_data_blob, now_str, s1_c])
        }).await.unwrap().unwrap();

        let conn_setup2 = pool.get().await.unwrap();
        let s1_c2 = space_id1.to_string();
        let p_data_blob2 = serde_json::to_vec(&json!({})).unwrap();
        let now_str2 = Utc::now().to_rfc3339();
        conn_setup2.interact(move |conn| {
            conn.execute("INSERT INTO pods (id, pod_type, pod_class, data, created_at, space) VALUES (?1, 't', 'c', ?2, ?3, ?4)", 
                         rusqlite::params!["another-pod", p_data_blob2, now_str2, s1_c2])
        }).await.unwrap().unwrap();

        let conn_setup3 = pool.get().await.unwrap();
        let s2_c = space_id2.to_string();
        let p_data_blob3 = serde_json::to_vec(&json!({})).unwrap();
        let now_str3 = Utc::now().to_rfc3339();
        conn_setup3.interact(move |conn| {
            conn.execute("INSERT INTO pods (id, pod_type, pod_class, data, created_at, space) VALUES (?1, 't', 'c', ?2, ?3, ?4)", 
                         rusqlite::params![pod_id2, p_data_blob3, now_str3, s2_c])
        }).await.unwrap().unwrap();

        let conn = pool.get().await.unwrap();
        let space1_id_clone = space_id1.to_string();
        let count1: i64 = conn
            .interact(move |conn_inner| {
                conn_inner.query_row(
                    "SELECT COUNT(*) FROM pods WHERE space = ?1",
                    [&space1_id_clone],
                    |r| r.get(0),
                )
            })
            .await
            .unwrap()
            .unwrap();
        assert_eq!(count1, 2);

        let conn_other = pool.get().await.unwrap();
        let space2_id_clone = space_id2.to_string();
        let count2: i64 = conn_other
            .interact(move |conn_inner| {
                conn_inner.query_row(
                    "SELECT COUNT(*) FROM pods WHERE space = ?1",
                    [&space2_id_clone],
                    |r| r.get(0),
                )
            })
            .await
            .unwrap()
            .unwrap();
        assert_eq!(count2, 1);

        assert_eq!(
            server
                .delete(&format!("/api/spaces/{}", space_id1))
                .await
                .status_code(),
            StatusCode::NO_CONTENT
        );

        let conn_after = pool.get().await.unwrap();
        let space1_id_clone_after = space_id1.to_string();
        let count1_after: i64 = conn_after
            .interact(move |conn_inner| {
                conn_inner.query_row(
                    "SELECT COUNT(*) FROM pods WHERE space = ?1",
                    [&space1_id_clone_after],
                    |r| r.get(0),
                )
            })
            .await
            .unwrap()
            .unwrap();
        assert_eq!(count1_after, 0);

        let conn_other_after = pool.get().await.unwrap();
        let space2_id_clone_after = space_id2.to_string();
        let count2_after: i64 = conn_other_after
            .interact(move |conn_inner| {
                conn_inner.query_row(
                    "SELECT COUNT(*) FROM pods WHERE space = ?1",
                    [&space2_id_clone_after],
                    |r| r.get(0),
                )
            })
            .await
            .unwrap()
            .unwrap();
        assert_eq!(count2_after, 1);

        let conn_final_check = pool.get().await.unwrap();
        let space1_id_final_clone = space_id1.to_string();
        let space1_exists: bool = conn_final_check
            .interact(move |conn_inner| {
                conn_inner
                    .query_row(
                        "SELECT 1 FROM spaces WHERE id = ?1",
                        [&space1_id_final_clone],
                        |_| Ok(true),
                    )
                    .optional()
                    .map(|r| r.is_some())
            })
            .await
            .unwrap()
            .unwrap();
        assert!(!space1_exists);
    }
}
