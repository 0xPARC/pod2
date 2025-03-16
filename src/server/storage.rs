use rusqlite::{Connection, Result as SqliteResult};

use super::types::Pod;

pub struct Database {
    conn: Connection,
}

impl Database {
    pub fn new(path: &str) -> SqliteResult<Self> {
        let conn = Connection::open(path)?;

        // Create tables if they don't exist
        conn.execute(
            "CREATE TABLE IF NOT EXISTS pods (
                id TEXT PRIMARY KEY,
                pod_type TEXT NOT NULL,
                data TEXT NOT NULL
            )",
            [],
        )?;

        Ok(Database { conn })
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
