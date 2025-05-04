use axum::{
    routing::{delete, get, post},
    Router,
};
use tower_http::trace::{DefaultMakeSpan, TraceLayer};

use crate::server::{db::ConnectionPool, handlers};

pub fn create_router(pool: ConnectionPool) -> Router {
    Router::new()
        .route("/api/pods/:space", get(handlers::list_pods_in_space))
        // Route for getting a single pod by ID in a space
        .route("/api/pods/:space/:id", get(handlers::get_pod_by_id))
        // New route for signing a POD
        .route("/api/pods/sign", post(handlers::sign_pod))
        .route("/api/hash", post(handlers::hash_string))
        // Add the connection pool as state
        .with_state(pool)
        // Add tracing layer for logging requests
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::default().include_headers(true)),
        )
}
