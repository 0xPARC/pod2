use axum::{
    routing::{delete, get, post},
    Router,
};
use tower_http::trace::{DefaultMakeSpan, TraceLayer};

use crate::server::{db::ConnectionPool, handlers};

pub fn create_router(pool: ConnectionPool) -> Router {
    Router::new()
        .route("/api/pods/:space", get(handlers::list_pods_in_space))
        .route("/api/pods/:space/:id", get(handlers::get_pod_by_id))
        .route("/api/pods/sign", post(handlers::sign_pod))
        //   .route("/api/pods/prove", post(handlers::prove_pod))
        .route("/api/hash", post(handlers::hash_string))
        .with_state(pool)
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::default().include_headers(true)),
        )
}
