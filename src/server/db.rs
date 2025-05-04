use anyhow::{Context, Result};
use deadpool_sqlite::{Config, Pool, Runtime};
use rusqlite::{Connection, Result as RusqliteResult};

// Type alias for the connection pool
pub type ConnectionPool = Pool;

/// Initializes the database connection pool using deadpool.
/// If `db_path` is `Some`, it opens or creates a database at that path.
/// If `db_path` is `None`, it creates an in-memory database.
pub async fn init_db_pool(db_path: Option<&str>) -> Result<ConnectionPool> {
    let path = db_path.unwrap_or(":memory:");
    let cfg = Config::new(path);
    let pool = cfg.create_pool(Runtime::Tokio1).context(format!(
        "Failed to build deadpool connection pool for '{}'",
        path
    ))?;

    // Run table creation on a dedicated connection from the pool
    // Using spawn_blocking as deadpool doesn't require create_pool to be async
    // and doesn't have a built-in interact equivalent for initial setup easily.
    let conn = pool
        .get()
        .await
        .context("Failed to get connection from pool for table creation")?;
    conn.interact(create_pods_table)
        .await
        // Explicitly format the error to ensure Send + Sync for anyhow::Error
        .map_err(|e| anyhow::anyhow!("InteractError: {}", e))
        .context("Database interaction failed during table creation")?
        .context("Failed to create 'pods' table using connection from pool")?;

    if path != ":memory:" {
        log::info!("Initialized deadpool database pool for '{}'", path);
    } else {
        log::info!("Initialized in-memory deadpool database pool");
    }

    Ok(pool)
}

// No change needed here, still takes a standard connection reference
fn create_pods_table(conn: &mut Connection) -> RusqliteResult<()> {
    conn.execute(
        "CREATE TABLE IF NOT EXISTS pods (
            id TEXT PRIMARY KEY,
            pod_type TEXT NOT NULL,
            pod_class TEXT NOT NULL,
            data BLOB NOT NULL,
            label TEXT,
            created_at TEXT NOT NULL,
            space TEXT NOT NULL
        )",
        (),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use tempfile::NamedTempFile;

    use super::*;

    // Helper function to check if the pods table exists
    // Needs to take &mut Connection for interact and return Result
    fn check_table_exists(conn: &mut Connection) -> Result<bool, rusqlite::Error> {
        conn.query_row(
            "SELECT name FROM sqlite_master WHERE type='table' AND name='pods'",
            [],
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
        let conn = pool
            .get()
            .await
            .expect("Failed to get connection from pool");
        let exists_result = conn
            .interact(check_table_exists)
            .await
            .expect("Interaction failed");
        let exists = exists_result.expect("check_table_exists failed"); // Explicitly get bool
        assert!(exists, "'pods' table should exist in in-memory DB");
    }

    #[tokio::test]
    async fn test_init_db_pool_file() {
        let temp_file = NamedTempFile::new().unwrap();
        let path_str = temp_file.path().to_str().unwrap();

        {
            let pool = init_db_pool(Some(path_str))
                .await
                .expect("Failed to initialize file DB pool");
            let conn = pool
                .get()
                .await
                .expect("Failed to get connection from pool");
            let exists_result = conn
                .interact(check_table_exists)
                .await
                .expect("Interaction failed");
            let exists = exists_result.expect("check_table_exists failed"); // Explicitly get bool
            assert!(exists, "'pods' table should exist in file DB");
            // Pool drops here, manager should handle connection closure
        }

        // Re-open the connection normally to check persistence (pool manager handles actual file)
        let conn2 = Connection::open(path_str).expect("Failed to reopen DB file");
        // Need mutable connection for helper
        let mut conn2_mut = conn2;
        assert!(
            check_table_exists(&mut conn2_mut).is_ok(),
            "'pods' table should persist in file DB",
        );
    }
}
