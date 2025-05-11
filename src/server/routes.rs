use axum::{
    routing::{delete, get, post},
    Router,
};
use tower_http::trace::{DefaultMakeSpan, TraceLayer};

use crate::server::{db::ConnectionPool, handlers};

pub fn create_router(pool: ConnectionPool) -> Router {
    Router::new()
        .route(
            "/api/pods/:space_id",
            get(handlers::pod_management::list_pods_in_space)
                .post(handlers::pod_management::import_pod_to_space),
        )
        .route(
            "/api/pods/:space_id/:pod_id",
            get(handlers::pod_management::get_pod_by_id)
                .delete(handlers::pod_management::delete_pod_from_space),
        )
        .route("/api/pods/sign", post(handlers::pod_management::sign_pod))
        //   .route("/api/pods/prove", post(handlers::playground::prove_pod)) // Assuming prove_pod would go to playground
        .route("/api/hash", post(handlers::pod_management::hash_string))
        // Playground API routes
        .route(
            "/api/validate",
            post(handlers::playground::validate_code_handler),
        )
        .route(
            "/api/execute",
            post(handlers::playground::execute_code_handler),
        )
        .route(
            "/api/executeMvp",
            post(handlers::playground::execute_mvp_handler),
        ) // Corrected from execute-mvp to executeMvp if the handler is named execute_mvp_handler
        // Spaces API routes
        .route(
            "/api/spaces",
            get(handlers::space_management::list_spaces)
                .post(handlers::space_management::create_space),
        )
        .route(
            "/api/spaces/:space_id",
            delete(handlers::space_management::delete_space),
        )
        .with_state(pool)
        .layer(
            TraceLayer::new_for_http()
                .make_span_with(DefaultMakeSpan::default().include_headers(true)),
        )
}
