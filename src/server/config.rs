use std::path::PathBuf;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Config {
    #[serde(default = "default_port")]
    pub port: u16,
    #[serde(default = "default_db_path")]
    pub db_path: String,
}

fn default_port() -> u16 {
    3001
}

fn default_db_path() -> String {
    "pod2.db".to_string()
}

impl Config {
    /// Loads configuration settings.
    ///
    /// Priority order (highest to lowest):
    /// 1. Override file specified by `config_path_override`.
    /// 2. `playground.toml` located in `base_dir` (or current working directory if `base_dir` is `None`).
    /// 3. Default values.
    pub fn load(
        config_path_override: Option<PathBuf>,
        base_dir: Option<PathBuf>,
    ) -> Result<Self, config::ConfigError> {
        let effective_base_dir = base_dir
            .unwrap_or_else(|| std::env::current_dir().expect("Failed to get current directory"));
        let playground_path = effective_base_dir.join("playground.toml");

        let mut settings = config::Config::builder()
            // Set defaults
            .set_default("port", default_port())?
            .set_default("db_path", default_db_path())?;

        // Load playground.toml if it exists and no override is provided
        if config_path_override.is_none() && playground_path.exists() {
            settings = settings.add_source(config::File::from(playground_path).required(false));
        }

        // Load override config file if provided
        // Note: config crate resolves relative paths against CWD by default.
        // If the override path is relative, it needs to be relative to the CWD
        // where the application is run, regardless of `base_dir`.
        if let Some(path) = config_path_override {
            settings = settings.add_source(config::File::from(path).required(true));
        }

        settings.build()?.try_deserialize()
    }
}

#[cfg(test)]
mod tests {
    use std::{fs::File, io::Write};

    use tempfile::tempdir;

    use super::*;

    #[test]
    fn test_load_defaults() {
        // Use a temporary directory unlikely to contain playground.toml
        let dir = tempdir().unwrap();
        let config = Config::load(None, Some(dir.path().to_path_buf()))
            .expect("Failed to load default config");
        assert_eq!(config.port, 3001);
        assert_eq!(config.db_path, "pod2.db");
    }

    #[test]
    fn test_load_from_playground_toml() {
        let dir = tempdir().unwrap();
        let file_path = dir.path().join("playground.toml");
        let mut file = File::create(&file_path).unwrap();
        writeln!(file, "port = 8080").unwrap();
        writeln!(file, "db_path = \"custom.db\"").unwrap();

        // Pass the temp dir as base_dir
        let config = Config::load(None, Some(dir.path().to_path_buf()))
            .expect("Failed to load config from playground.toml");
        assert_eq!(config.port, 8080);
        assert_eq!(config.db_path, "custom.db");
    }

    #[test]
    fn test_load_from_override_path() {
        let dir = tempdir().unwrap();
        let file_path = dir.path().join("custom_config.toml");
        let mut file = File::create(&file_path).unwrap();
        writeln!(file, "port = 9999").unwrap();
        // Omit db_path to test default fallback with override file

        // Pass the absolute path to the override file
        // base_dir is irrelevant here as override takes precedence
        let config = Config::load(Some(file_path.canonicalize().unwrap()), None)
            .expect("Failed to load config from override path");
        assert_eq!(config.port, 9999);
        assert_eq!(config.db_path, "pod2.db"); // Should use default
    }

    #[test]
    fn test_load_override_takes_precedence() {
        let dir = tempdir().unwrap();

        // Create playground.toml in the temp dir
        let playground_path = dir.path().join("playground.toml");
        let mut playground_file = File::create(&playground_path).unwrap();
        writeln!(playground_file, "port = 1111").unwrap();
        writeln!(playground_file, "db_path = \"playground.db\"").unwrap();

        // Create override config in the temp dir
        let override_path = dir.path().join("override.toml");
        let mut override_file = File::create(&override_path).unwrap();
        writeln!(override_file, "port = 2222").unwrap();
        // db_path omitted in override

        // Pass override path and base_dir for playground.toml
        let config = Config::load(
            Some(override_path.canonicalize().unwrap()),
            Some(dir.path().to_path_buf()),
        )
        .expect("Failed to load config with override");

        // Override port should be used, default db_path should be used
        assert_eq!(config.port, 2222);
        assert_eq!(config.db_path, "pod2.db");
    }
}
