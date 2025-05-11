use axum::{http::StatusCode, response::IntoResponse};

pub mod playground;
pub mod pod_management;
pub mod space_management;

pub enum AppError {
    DatabaseError(anyhow::Error),
    NotFound(String),
}

// Tell axum how to convert `AppError` into a response.
impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        match self {
            AppError::DatabaseError(err) => {
                log::error!("Application error: {:#}", err);
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    format!("Something went wrong: {}", err),
                )
                    .into_response()
            }
            AppError::NotFound(msg) => {
                log::warn!("Resource not found: {}", msg);
                (StatusCode::NOT_FOUND, msg).into_response()
            }
        }
    }
}

impl From<anyhow::Error> for AppError {
    fn from(err: anyhow::Error) -> Self {
        // Attempt to downcast to rusqlite::Error to check for QueryReturnedNoRows
        // This specific check might be better handled within individual handlers
        // if the context of "not found" is important.
        // For a general From<anyhow::Error>, just wrapping it is safer.
        AppError::DatabaseError(err)
    }
}
