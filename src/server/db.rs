use anyhow::{Context, Result};
use deadpool_sqlite::{Config, Pool, Runtime};
use log::info;
use uuid::Uuid;

// Type alias for the connection pool
pub type ConnectionPool = Pool;

/// Initializes the database connection pool using deadpool.
/// If `path` is `Some`, it opens or creates a database at that path.
/// If `path` is `None`, it creates an in-memory database.
pub async fn init_db_pool(path: Option<&str>) -> Result<ConnectionPool> {
    let db_path = match path {
        Some(p) => p.to_string(),
        None => {
            let unique_name = Uuid::new_v4().to_string();
            // Use a uniquely named, shared-cache in-memory database for each pool instance
            // when no path is specified. This ensures test isolation if each test creates its own pool.
            format!("file:{unique_name}?mode=memory&cache=shared")
        }
    };
    info!("Initializing database pool with path: {}", db_path);

    let config = Config::new(db_path);
    let pool = config.create_pool(Runtime::Tokio1)?;
    Ok(pool)
}

/// Creates the database schema (tables) if they don't already exist.
pub async fn create_schema(pool: &ConnectionPool) -> Result<()> {
    let conn = pool
        .get()
        .await
        .context("Failed to get connection for schema creation")?;
    let _ = conn
        .interact(|conn_inner| {
            info!("Creating spaces table...");
            conn_inner.execute(
                "CREATE TABLE IF NOT EXISTS spaces (
                id TEXT PRIMARY KEY,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP
            )",
                [],
            )?;

            info!("Creating pods table...");
            conn_inner.execute(
                "CREATE TABLE IF NOT EXISTS pods (
                id TEXT NOT NULL,
                pod_type TEXT NOT NULL,
                data BLOB NOT NULL,
                label TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                space TEXT NOT NULL,
                PRIMARY KEY (space, id),
                FOREIGN KEY (space) REFERENCES spaces(id) ON DELETE CASCADE
            )",
                [],
            )?;
            Ok::<_, rusqlite::Error>(())
        })
        .await
        .map_err(|e| anyhow::anyhow!("InteractError during schema creation: {}", e))
        .context("Failed to create tables")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use rusqlite::Connection;
    use tempfile::NamedTempFile;

    use super::*;

    // Helper function to check if the pods table exists
    // Needs to take &mut Connection for interact and return Result
    fn check_table_exists(
        conn: &mut Connection,
        table_name: &str,
    ) -> Result<bool, rusqlite::Error> {
        conn.query_row(
            "SELECT name FROM sqlite_master WHERE type='table' AND name= ?1",
            [table_name],
            |_| Ok(true), // Returns Ok(true) on success
        )
        // If query_row returns Err(QueryReturnedNoRows), it means the table doesn't exist.
        .map(|_| true) // Map Ok(true) to just true
        .or_else(|err| {
            if matches!(err, rusqlite::Error::QueryReturnedNoRows) {
                Ok(false) // Table doesn't exist
            } else {
                Err(err) // Other DB error
            }
        })
    }

    #[tokio::test]
    async fn test_init_db_pool_in_memory() {
        let pool = init_db_pool(None)
            .await
            .expect("Failed to initialize in-memory DB pool");

        create_schema(&pool)
            .await
            .expect("Failed to create schema for in-memory DB");

        let conn = pool
            .get()
            .await
            .expect("Failed to get connection from pool");
        let exists_result = conn
            .interact(|conn| check_table_exists(conn, "pods"))
            .await
            .expect("Interaction failed for pods table");
        let pods_exists = exists_result.expect("check_table_exists for pods failed");
        assert!(
            pods_exists,
            "'pods' table should exist in in-memory DB after schema creation"
        );

        let spaces_exists_result = conn
            .interact(|conn| check_table_exists(conn, "spaces"))
            .await
            .expect("Interaction failed for spaces table");
        let spaces_exists = spaces_exists_result.expect("check_table_exists for spaces failed");
        assert!(
            spaces_exists,
            "'spaces' table should exist in in-memory DB after schema creation"
        );
    }

    #[tokio::test]
    async fn test_init_db_pool_file() {
        let temp_file = NamedTempFile::new().unwrap();
        let path_str = temp_file.path().to_str().unwrap();

        {
            let pool = init_db_pool(Some(path_str))
                .await
                .expect("Failed to initialize file DB pool");

            create_schema(&pool)
                .await
                .expect("Failed to create schema for file DB");

            let conn = pool
                .get()
                .await
                .expect("Failed to get connection from pool");
            let exists_result = conn
                .interact(|conn| check_table_exists(conn, "pods"))
                .await
                .expect("Interaction failed for pods table");
            let pods_exists = exists_result.expect("check_table_exists for pods failed"); // Explicitly get bool
            assert!(
                pods_exists,
                "'pods' table should exist in file DB after schema creation"
            );

            let spaces_exists_result = conn
                .interact(|conn| check_table_exists(conn, "spaces"))
                .await
                .expect("Interaction failed for spaces table");
            let spaces_exists = spaces_exists_result.expect("check_table_exists for spaces failed");
            assert!(
                spaces_exists,
                "'spaces' table should exist in file DB after schema creation"
            );
            // Pool drops here, manager should handle connection closure
        }

        // Re-open the connection normally to check persistence (pool manager handles actual file)
        let conn2 = Connection::open(path_str).expect("Failed to reopen DB file");
        // Need mutable connection for helper
        let mut conn2_mut = conn2;
        assert!(
            check_table_exists(&mut conn2_mut, "pods").expect("check_table_exists for pods failed"),
            "'pods' table should persist in file DB",
        );
        assert!(
            check_table_exists(&mut conn2_mut, "spaces")
                .expect("check_table_exists for spaces failed"),
            "'spaces' table should persist in file DB",
        );
    }
}
