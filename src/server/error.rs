use axum::http::StatusCode;
use std::fmt;

#[derive(Debug)]
pub enum ServerError {
    PodNotFound(String),
    FrontendError(anyhow::Error),
    DatabaseError(String),
}

impl fmt::Display for ServerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ServerError::PodNotFound(id) => write!(f, "Pod not found: {}", id),
            ServerError::FrontendError(e) => write!(f, "Frontend error: {}", e),
            ServerError::DatabaseError(e) => write!(f, "Database error: {}", e),
        }
    }
}

impl std::error::Error for ServerError {}

impl From<anyhow::Error> for ServerError {
    fn from(err: anyhow::Error) -> Self {
        ServerError::FrontendError(err)
    }
}

impl axum::response::IntoResponse for ServerError {
    fn into_response(self) -> axum::response::Response {
        let (status, error_message) = match self {
            ServerError::PodNotFound(_) => (StatusCode::NOT_FOUND, self.to_string()),
            ServerError::FrontendError(_) => (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()),
            ServerError::DatabaseError(_) => (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()),
        };

        let body = axum::Json(serde_json::json!({
            "error": error_message,
        }));

        (status, body).into_response()
    }
}
