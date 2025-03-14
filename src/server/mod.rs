use axum::{routing::post, Router};
use axum_server::bind;
use std::sync::Arc;
use tokio::sync::Mutex;
use tower_http::cors::{Any, CorsLayer};

mod error;
mod handlers;
#[cfg(test)]
mod tests;
mod types;

pub use error::ServerError;
pub use types::*;

use crate::{
    backends::plonky2::mock_signed::MockSigner, frontend::SignedPodBuilder, middleware::Params,
};

pub async fn start_server() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::fmt::init();

    // Create CORS layer
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([axum::http::Method::POST])
        .allow_headers(Any);

    // Create shared state
    let state = Arc::new(Mutex::new(ServerState::new()));

    let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
    signed_pod_builder.insert("number", 1);
    let mut signer = MockSigner {
        pk: "test_signer".into(),
    };
    let pod = signed_pod_builder.sign(&mut signer)?;
    {
        let mut state_lock = state.lock().await;
        let id_string = format!("{:x}", pod.id());
        state_lock.signed_pods.insert(id_string, pod);
    }

    let mut signed_pod_builder = SignedPodBuilder::new(&Params::default());
    signed_pod_builder.insert("other_number", 1);
    let pod = signed_pod_builder.sign(&mut signer)?;
    {
        let mut state_lock = state.lock().await;
        let id_string = format!("{:x}", pod.id());
        state_lock.signed_pods.insert(id_string, pod);
    }

    // Build router
    let app = Router::new()
        .route("/api/list-pods", post(handlers::list_pods))
        .route("/api/get-pod", post(handlers::get_pod))
        .route("/api/create-signed-pod", post(handlers::create_signed_pod))
        .route("/api/create-main-pod", post(handlers::create_main_pod))
        .route("/api/delete-pod", post(handlers::delete_pod))
        .route("/api/import-pod", post(handlers::import_pod))
        .route(
            "/api/validate-statement",
            post(handlers::validate_statement),
        )
        .route(
            "/api/validate-statements",
            post(handlers::validate_statements),
        )
        .layer(cors)
        .with_state(state);

    // Start server
    let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 3000));
    tracing::info!("listening on {}", addr);
    bind(addr).serve(app.into_make_service()).await?;

    Ok(())
}
