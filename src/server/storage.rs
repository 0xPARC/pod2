use rusqlite::{Connection, Result as SqliteResult};

use super::types::Pod;

pub struct Database {
    conn: Connection,
}

impl Database {
    pub fn new(path: &str) -> SqliteResult<Self> {
        let conn = Connection::open(path)?;

        // Create version table if it doesn't exist
        conn.execute(
            "CREATE TABLE IF NOT EXISTS schema_version (
                version INTEGER PRIMARY KEY
            )",
            [],
        )?;

        // Check if version exists, if not initialize it
        let version_exists: bool =
            conn.query_row("SELECT EXISTS(SELECT 1 FROM schema_version)", [], |row| {
                row.get(0)
            })?;

        if !version_exists {
            conn.execute("INSERT INTO schema_version (version) VALUES (0)", [])?;
        }

        let db = Database { conn };
        db.run_migrations()?;
        Ok(db)
    }

    fn run_migrations(&self) -> SqliteResult<()> {
        let mut current_version: i64 =
            self.conn
                .query_row("SELECT version FROM schema_version", [], |row| row.get(0))?;

        // List of migrations to apply in order
        let migrations = vec![
            // Migration 0 -> 1: Initial schema
            "CREATE TABLE IF NOT EXISTS pods (
                id TEXT PRIMARY KEY,
                pod_type TEXT NOT NULL,
                data TEXT NOT NULL
            )",
            // Add new migrations here as needed, for example:
            // "ALTER TABLE pods ADD COLUMN created_at TEXT"
        ];

        let mut migrations_run = false;

        // Apply any pending migrations
        for (version, migration) in migrations.iter().enumerate() {
            let version = version as i64 + 1;
            if version > current_version {
                println!("Running migration v{}...", version);
                self.conn.execute(migration, [])?;
                // Update the version number
                self.conn
                    .execute("UPDATE schema_version SET version = ?1", [version])?;
                current_version = version;
                migrations_run = true;
            }
        }

        if !migrations_run {
            println!("Database already up-to-date (v{})", current_version);
        } else {
            println!("Database migrated to v{}", current_version);
        }

        Ok(())
    }

    pub fn store_pod(&self, id: &str, pod: &Pod) -> Result<(), Box<dyn std::error::Error>> {
        let pod_type = match pod {
            Pod::Signed(_) => "signed",
            Pod::Main(_) => "main",
        };
        let data = serde_json::to_string(pod)?;

        self.conn.execute(
            "INSERT OR REPLACE INTO pods (id, pod_type, data) VALUES (?1, ?2, ?3)",
            [id, pod_type, &data],
        )?;

        Ok(())
    }

    pub fn get_pod(&self, id: &str) -> Result<Option<Pod>, Box<dyn std::error::Error>> {
        let mut stmt = self
            .conn
            .prepare("SELECT pod_type, data FROM pods WHERE id = ?1")?;

        let result = stmt.query_row([id], |row| {
            let pod_type: String = row.get(0)?;
            let data: String = row.get(1)?;
            Ok((pod_type, data))
        });

        match result {
            Ok((_, data)) => Ok(Some(serde_json::from_str(&data)?)),
            Err(rusqlite::Error::QueryReturnedNoRows) => Ok(None),
            Err(e) => Err(Box::new(e)),
        }
    }

    pub fn list_pods(&self) -> Result<Vec<Pod>, Box<dyn std::error::Error>> {
        let mut stmt = self.conn.prepare("SELECT data FROM pods")?;
        let pods = stmt
            .query_map([], |row| {
                let data: String = row.get(0)?;
                serde_json::from_str(&data)
                    .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(e)))
            })?
            .collect::<Result<Vec<Pod>, _>>()?;

        Ok(pods)
    }

    pub fn delete_pod(&self, id: &str) -> SqliteResult<bool> {
        let count = self.conn.execute("DELETE FROM pods WHERE id = ?1", [id])?;
        Ok(count > 0)
    }
}
