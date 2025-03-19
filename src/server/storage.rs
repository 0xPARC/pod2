use rusqlite::{Connection, Result as SqliteResult};

use super::types::{Pod, PodVariant};

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

        let mut db = Database { conn };
        db.run_migrations()?;
        Ok(db)
    }

    fn run_migrations(&mut self) -> SqliteResult<()> {
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
            // Add nicknames to PODs
            "ALTER TABLE pods ADD COLUMN nickname TEXT",
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_nickname ON pods (nickname)",
            // Divide PODs into "spaces", with "default" being the default
            // Existing PODs will be added to "default"
            "ALTER TABLE pods ADD COLUMN space TEXT NOT NULL DEFAULT 'default'",
            "CREATE INDEX IF NOT EXISTS idx_space ON pods (space)",
            // Store creation time of PODs
            "ALTER TABLE pods ADD COLUMN created_at TIMESTAMP",
            "UPDATE pods SET created_at = CURRENT_TIMESTAMP",
            "CREATE INDEX IF NOT EXISTS idx_created_at ON pods (created_at)",
            // Make created_at NOT NULL with default
            "CREATE TABLE pods_new (
                id TEXT PRIMARY KEY,
                pod_type TEXT NOT NULL,
                data TEXT NOT NULL,
                nickname TEXT,
                space TEXT NOT NULL DEFAULT 'default',
                created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP
            )",
            "INSERT INTO pods_new (id, pod_type, data, nickname, space) SELECT id, pod_type, data, nickname, space FROM pods",
            "DROP TABLE pods",
            "ALTER TABLE pods_new RENAME TO pods",
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_nickname ON pods (nickname)",
            "CREATE INDEX IF NOT EXISTS idx_space ON pods (space)",
            "CREATE INDEX IF NOT EXISTS idx_created_at ON pods (created_at)",
        ];

        let mut migrations_run = false;

        // Start a transaction for all pending migrations
        let tx = self.conn.transaction()?;

        // Apply any pending migrations
        for (version, migration) in migrations.iter().enumerate() {
            let version = version as i64 + 1;
            if version > current_version {
                println!("Running migration v{}...", version);
                tx.execute(migration, [])?;
                // Update the version number
                tx.execute("UPDATE schema_version SET version = ?1", [version])?;
                current_version = version;
                migrations_run = true;
            }
        }

        // Commit all migrations at once
        tx.commit()?;

        if !migrations_run {
            println!("Database already up-to-date (v{})", current_version);
        } else {
            println!("Database migrated to v{}", current_version);
        }

        Ok(())
    }

    pub fn store_pod(&self, id: &str, pod: &Pod) -> Result<(), Box<dyn std::error::Error>> {
        let pod_type = match &pod.pod {
            PodVariant::Signed(_) => "signed",
            PodVariant::Main(_) => "main",
        };
        let data = serde_json::to_string(pod)?;

        // If nickname is provided, ensure it's unique
        if let Some(ref nickname) = pod.nickname {
            let existing_id: Option<String> = self
                .conn
                .query_row(
                    "SELECT id FROM pods WHERE nickname = ?1 AND id != ?2",
                    [nickname, id],
                    |row| row.get(0),
                )
                .ok();

            if let Some(existing_id) = existing_id {
                return Err(format!(
                    "Nickname '{}' is already in use by pod {}",
                    nickname, existing_id
                )
                .into());
            }
        }

        // Check if pod exists to determine if we should set created_at
        let exists: bool = self.conn.query_row(
            "SELECT EXISTS(SELECT 1 FROM pods WHERE id = ?1)",
            [id],
            |row| row.get(0),
        )?;

        if exists {
            // Update existing pod, preserving created_at
            self.conn.execute(
                "UPDATE pods SET pod_type = ?1, data = ?2, nickname = ?3 WHERE id = ?4",
                [pod_type, &data, &pod.nickname.as_deref().unwrap_or(""), id],
            )?;
        } else {
            // Insert new pod with current timestamp
            self.conn.execute(
                "INSERT INTO pods (id, pod_type, data, nickname, created_at) VALUES (?1, ?2, ?3, ?4, CURRENT_TIMESTAMP)",
                [id, pod_type, &data, &pod.nickname.as_deref().unwrap_or("")],
            )?;
        }

        Ok(())
    }

    pub fn get_pod(&self, id: &str) -> Result<Option<Pod>, Box<dyn std::error::Error>> {
        let mut stmt = self
            .conn
            .prepare("SELECT pod_type, data, nickname FROM pods WHERE id = ?1")?;

        let result = stmt.query_row([id], |row| {
            let pod_type: String = row.get(0)?;
            let data: String = row.get(1)?;
            let nickname: Option<String> = row.get(2)?;
            Ok((pod_type, data, nickname))
        });

        match result {
            Ok((_, data, nickname)) => {
                let mut pod: Pod = serde_json::from_str(&data)?;
                pod.nickname = nickname.filter(|n| !n.is_empty());
                Ok(Some(pod))
            }
            Err(rusqlite::Error::QueryReturnedNoRows) => Ok(None),
            Err(e) => Err(Box::new(e)),
        }
    }

    pub fn list_pods(&self) -> Result<Vec<Pod>, Box<dyn std::error::Error>> {
        let mut stmt = self
            .conn
            .prepare("SELECT data, nickname FROM pods ORDER BY created_at DESC")?;
        let pods = stmt
            .query_map([], |row| {
                let data: String = row.get(0)?;
                let nickname: Option<String> = row.get(1)?;
                let mut pod: Pod = serde_json::from_str(&data)
                    .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(e)))?;
                pod.nickname = nickname.filter(|n| !n.is_empty());
                Ok(pod)
            })?
            .collect::<Result<Vec<Pod>, _>>()?;

        Ok(pods)
    }

    pub fn delete_pod(&self, id: &str) -> SqliteResult<bool> {
        let count = self.conn.execute("DELETE FROM pods WHERE id = ?1", [id])?;
        Ok(count > 0)
    }
}
