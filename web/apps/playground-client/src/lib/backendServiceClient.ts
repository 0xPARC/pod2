import { useAppStore } from './store';

// --- Type definitions (mirroring Rust structs from src/server/api_types.rs) ---

export enum DiagnosticSeverity {
  Error = 'Error',
  Warning = 'Warning',
  Information = 'Information',
  Hint = 'Hint',
}

export interface Diagnostic {
  message: string;
  severity: DiagnosticSeverity;
  start_line: number; // 1-indexed
  start_column: number; // 1-indexed
  end_line: number; // 1-indexed
  end_column: number; // 1-indexed
}

export interface ValidateCodeRequest {
  code: string;
}

export interface ValidateCodeResponse {
  diagnostics: Diagnostic[];
}

export interface ExecuteCodeRequest {
  code: string;
}

// Assuming the success response for execute might be a generic JSON value for now
// and error response structure might be similar to validation or a simpler error message.
export interface ExecuteCodeResponse {
  // Define based on actual backend response for MVP, e.g.:
  // status: string;
  // result?: any; // Placeholder
  // error?: string;
  // details?: string;
  [key: string]: any; // For MVP, allow any JSON structure
}

const API_BASE_URL = '/api'; // Assuming Vite proxy or same-origin deployment

/**
 * Validates Podlog code using the backend service.
 * @param source The Podlog code to validate.
 * @returns A promise that resolves to the validation response.
 */
export async function validateCode(source: string): Promise<ValidateCodeResponse> {
  try {
    const requestPayload: ValidateCodeRequest = { code: source };
    const response = await fetch(`${API_BASE_URL}/validate`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestPayload),
    });

    if (!response.ok) {
      // Try to parse error body if backend provides one
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails = errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      // For validation, even on HTTP error, backend might send diagnostics
      // If status is 400 (Bad Request), it's likely a validation failure with diagnostics
      if (response.status === 400) {
        try {
          const errorData = await response.json() as ValidateCodeResponse;
          if (errorData.diagnostics) {
            useAppStore.getState().setIsBackendConnected(true); // It responded, so it's connected
            return errorData;
          }
        } catch (e) { /* fall through */ }
      }
      throw new Error(errorDetails);
    }

    const data: ValidateCodeResponse = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return data;
  } catch (error) {
    console.error('Error calling validate API:', error);
    useAppStore.getState().setIsBackendConnected(false);
    // Return a response with a generic error diagnostic
    return {
      diagnostics: [
        {
          message: error instanceof Error ? error.message : 'Failed to connect to validation service',
          severity: DiagnosticSeverity.Error,
          start_line: 1,
          start_column: 1,
          end_line: 1,
          end_column: 1,
        },
      ],
    };
  }
}

/**
 * Executes Podlog code using the backend service.
 * @param source The Podlog code to execute.
 * @returns A promise that resolves to the execution response.
 */
export async function executeCode(source: string): Promise<ExecuteCodeResponse> {
  try {
    const requestPayload: ExecuteCodeRequest = { code: source };
    const response = await fetch(`${API_BASE_URL}/executeMvp`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(requestPayload),
    });

    if (!response.ok) {
      // Attempt to get more detailed error from backend
      let errorJson;
      try {
        errorJson = await response.json();
      } catch (e) { /* ignore */ }

      const errorMessage = errorJson?.error || `HTTP error ${response.status}`;
      throw new Error(errorMessage);
    }
    useAppStore.getState().setIsBackendConnected(true);
    return await response.json() as ExecuteCodeResponse;
  } catch (error) {
    console.error('Error calling execute API:', error);
    useAppStore.getState().setIsBackendConnected(false);
    // For execute, we might want to throw and let the caller handle UI update
    // Or return a structured error response if your ExecuteCodeResponse can model it
    throw error; // Re-throw for now, can be refined
  }
}

// Optional: A simple health check or initial ping to set isBackendConnected
export async function checkBackendConnection() {
  try {
    // A lightweight endpoint like /api/health or even a successful /api/validate with empty code
    // For now, we'll rely on the first actual call to validate/execute to set connection status.
    // Alternatively, one could make a HEAD request or an OPTIONS request if the server supports it.
    // For this MVP, we assume first successful validate/execute means connected.
    // To be more proactive, one could add a dedicated health endpoint on the backend.
    // console.log("Checking backend connection (not implemented, relies on first API call).");
  } catch (error) {
    useAppStore.getState().setIsBackendConnected(false);
  }
}

// Call checkBackendConnection on load (optional, and might be too eager)
// checkBackendConnection(); 