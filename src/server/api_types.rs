use serde::{Deserialize, Serialize};

// --- Validation Structures ---

#[derive(Deserialize, Debug)]
pub struct ValidateCodeRequest {
    pub code: String,
}

#[derive(Serialize, Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub severity: DiagnosticSeverity,
    pub start_line: usize,   // 1-based
    pub start_column: usize, // 1-based
    pub end_line: usize,     // 1-based
    pub end_column: usize,   // 1-based
}

#[derive(Serialize, Debug, Clone)]
pub enum DiagnosticSeverity {
    Error,
    // In the future, we can add: Warning, Information, Hint
}

#[derive(Serialize, Debug, Clone)]
pub struct ValidateCodeResponse {
    pub diagnostics: Vec<Diagnostic>,
}

// --- Execution Structures ---

#[derive(Deserialize, Debug)]
pub struct ExecuteMvpRequest {
    pub code: String,
}

#[derive(Deserialize, Debug)]
pub struct ExecuteCodeRequest {
    pub code: String,
    pub space_id: String,
}

// For a successful execution, the response body will be `Json<serde_json::Value>`
// where the `serde_json::Value` is a JSON string containing the execution result.
// Errors during execution (including validation errors if code is invalid)
// will be handled by a new `PlaygroundApiError` type returned by the handlers.
