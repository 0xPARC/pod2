use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;
use pod2::server::{config::Config, db, handlers::playground, routes};
use tokio::net::TcpListener;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Optional path to a configuration file
    #[arg(short, long, value_name = "FILE")]
    config: Option<PathBuf>,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize logging
    // Use RUST_LOG=info,pod2_server=debug,tower_http=debug for detailed tracing
    env_logger::init();

    let args = Args::parse();

    // Load configuration
    let config = Config::load(args.config, None).context("Failed to load configuration")?;

    log::info!("Loaded configuration: {:?}", config);

    // Initialize database pool (init_db_pool is now async)
    let db_pool = db::init_db_pool(Some(&config.db_path))
        .await
        .context("Failed to initialize database pool")?;

    db::create_schema(&db_pool)
        .await
        .context("Failed to create schema")?;

    playground::setup_zukyc_space(&db_pool)
        .await
        .context("Failed to setup Zukyc space")?;

    // Create the Axum router
    let app = routes::create_router(db_pool);

    // Bind the server to the address
    let addr = format!("0.0.0.0:{}", config.port);
    let listener = TcpListener::bind(&addr)
        .await
        .context(format!("Failed to bind TCP listener to {}", addr))?;
    log::info!("Server listening on {}", addr);

    // Start the server
    axum::serve(listener, app.into_make_service())
        .await
        .context("Axum server failed")?;

    Ok(())
}
