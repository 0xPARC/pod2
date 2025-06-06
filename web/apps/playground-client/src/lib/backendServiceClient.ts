import { useAppStore } from "./store";
import type {
  SpaceInfo,
  PodInfo,
  MainPod,
  SignedPod,
  Value,
} from "@/types/pod2";

// --- Type definitions (mirroring Rust structs from src/server/api_types.rs) ---

export enum DiagnosticSeverity {
  Error = "Error",
  Warning = "Warning",
  Information = "Information",
  Hint = "Hint",
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
  space_id: string;
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

const API_BASE_URL = "/api"; // Assuming Vite proxy or same-origin deployment

/**
 * Validates Podlog code using the backend service.
 * @param source The Podlog code to validate.
 * @returns A promise that resolves to the validation response.
 */
export async function validateCode(
  source: string
): Promise<ValidateCodeResponse> {
  try {
    const requestPayload: ValidateCodeRequest = { code: source };
    const response = await fetch(`${API_BASE_URL}/validate`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(requestPayload),
    });

    if (!response.ok) {
      // Try to parse error body if backend provides one
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      // For validation, even on HTTP error, backend might send diagnostics
      // If status is 400 (Bad Request), it's likely a validation failure with diagnostics
      if (response.status === 400) {
        try {
          const errorData = (await response.json()) as ValidateCodeResponse;
          if (errorData.diagnostics) {
            useAppStore.getState().setIsBackendConnected(true); // It responded, so it's connected
            return errorData;
          }
        } catch (e) {
          /* fall through */
        }
      }
      throw new Error(errorDetails);
    }

    const data: ValidateCodeResponse = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return data;
  } catch (error) {
    console.error("Error calling validate API:", error);
    useAppStore.getState().setIsBackendConnected(false);
    // Return a response with a generic error diagnostic
    return {
      diagnostics: [
        {
          message:
            error instanceof Error
              ? error.message
              : "Failed to connect to validation service",
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
export async function executeCode(
  source: string,
  spaceId: string
): Promise<ExecuteCodeResponse> {
  try {
    const requestPayload: ExecuteCodeRequest = {
      code: source,
      space_id: spaceId,
    };
    const response = await fetch(`${API_BASE_URL}/execute`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(requestPayload),
    });

    if (!response.ok) {
      // Attempt to get more detailed error from backend
      let errorJson;
      try {
        errorJson = await response.json();
      } catch (e) {
        /* ignore */
      }

      const errorMessage = errorJson?.error || `HTTP error ${response.status}`;
      throw new Error(errorMessage);
    }
    useAppStore.getState().setIsBackendConnected(true);
    return (await response.json()) as ExecuteCodeResponse;
  } catch (error) {
    console.error("Error calling execute API:", error);
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

// --- New functions for Spaces and PODs ---

/**
 * Fetches the list of available spaces from the backend.
 * @returns A promise that resolves to an array of SpaceInfo objects.
 */
export async function listSpaces(): Promise<SpaceInfo[]> {
  try {
    const response = await fetch(`${API_BASE_URL}/spaces`, {
      method: "GET",
      headers: {
        Accept: "application/json", // Important for content negotiation
      },
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      throw new Error(errorDetails);
    }

    const data: SpaceInfo[] = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return data;
  } catch (error) {
    console.error("Error calling listSpaces API:", error);
    useAppStore.getState().setIsBackendConnected(false);
    // For listSpaces, re-throwing the error might be better than returning an empty array,
    // as the consuming hook can handle the error state.
    throw error;
  }
}

/**
 * Fetches the list of PODs within a specific space from the backend.
 * @param spaceId The ID of the space to fetch PODs from.
 * @returns A promise that resolves to an array of PodInfo objects.
 */
export async function listPodsInSpace(spaceId: string): Promise<PodInfo[]> {
  if (!spaceId) {
    // Or throw an error, or handle as the caller expects.
    // Returning an empty array if spaceId is invalid/nullish to prevent API call.
    console.warn(
      "listPodsInSpace called with no spaceId, returning empty array."
    );
    return Promise.resolve([]);
  }
  try {
    const response = await fetch(`${API_BASE_URL}/pods/${spaceId}`, {
      method: "GET",
      headers: {
        Accept: "application/json",
      },
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      throw new Error(errorDetails);
    }

    const data: PodInfo[] = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return data;
  } catch (error) {
    console.error(
      `Error calling listPodsInSpace API for space ${spaceId}:`,
      error
    );
    useAppStore.getState().setIsBackendConnected(false);
    throw error; // Re-throw for the hook to handle
  }
}

// --- Client-side specific payload for importing a MainPod ---
export interface ImportPodClientPayload {
  podType: "main" | "signed"; // To distinguish between MainPod and SignedPod
  data: MainPod | Omit<SignedPod, "id" | "verify">; // Use MainPod or SignedPod from types/pod2.d.ts. For SignedPod, we might not have id/verify on client before sending.
  label?: string;
}

/**
 * Imports a Pod (MainPod or SignedPod) into a specified space.
 * The backend will generate the deterministic POD ID.
 * @param spaceId The ID of the space to import the POD into.
 * @param payload The details of the POD to import.
 * @returns A promise that resolves to the PodInfo of the created POD.
 */
export async function importPodDataToSpace(
  spaceId: string,
  payload: ImportPodClientPayload
): Promise<PodInfo> {
  if (!spaceId) {
    throw new Error("spaceId is required to import a POD.");
  }

  // The backend expects payload.data to be the MainPodHelper or SignedPodHelper structure.
  // The payload we construct here has `data` as a MainPod or SignedPod object.
  // The backend's ImportPodRequest expects `pod_type: String`, `pod_class: String`, `data: serde_json::Value`, `label: Option<String>`
  // So we need to ensure the `payload` sent in the body matches that structure.

  const backendPayload = {
    podType: payload.podType,
    data: payload.data, // This should be serialized by JSON.stringify automatically
    label: payload.label,
  };

  try {
    const response = await fetch(`${API_BASE_URL}/pods/${spaceId}`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Accept: "application/json",
      },
      body: JSON.stringify(backendPayload), // Send the constructed backendPayload
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      throw new Error(errorDetails);
    }

    const createdPodInfo: PodInfo = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return createdPodInfo;
  } catch (error) {
    console.error(
      `Error calling importPodDataToSpace API for space ${spaceId}:`,
      error
    );
    useAppStore.getState().setIsBackendConnected(false);
    throw error;
  }
}

/**
 * Deletes a specific POD from a given space.
 * @param spaceId The ID of the space from which to delete the POD.
 * @param podId The ID of the POD to delete.
 * @returns A promise that resolves when the POD is successfully deleted.
 * @throws Will throw an error if the API call fails.
 */
export async function deletePodFromSpace(
  spaceId: string,
  podId: string
): Promise<void> {
  if (!spaceId || !podId) {
    throw new Error("spaceId and podId are required to delete a POD.");
  }

  try {
    const response = await fetch(`${API_BASE_URL}/pods/${spaceId}/${podId}`, {
      method: "DELETE",
      headers: {
        Accept: "application/json", // Or appropriate if no content is expected
      },
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        // Try to get more specific error from backend if available
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // If response body is not JSON or empty, use the HTTP status
      }
      // Specific check for 404 if needed, otherwise a generic error
      if (response.status === 404) {
        throw new Error(
          `POD with id '${podId}' not found in space '${spaceId}'.`
        );
      }
      throw new Error(errorDetails);
    }

    // DELETE typically returns 204 No Content on success, so no JSON body to parse.
    // If it returns 200 OK with a body, response.json() would be needed.
    useAppStore.getState().setIsBackendConnected(true);
    // No return value needed for a successful delete typically
  } catch (error) {
    console.error(
      `Error calling deletePodFromSpace API for space '${spaceId}', pod '${podId}':`,
      error
    );
    useAppStore.getState().setIsBackendConnected(false);
    throw error; // Re-throw for the caller to handle
  }
}

/**
 * Creates a new space.
 * @param spaceId The ID of the space to create.
 * @returns A promise that resolves when the space is created.
 */
export async function createSpace(spaceId: string): Promise<Response> {
  try {
    const response = await fetch(`${API_BASE_URL}/spaces`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify({ id: spaceId }),
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore
      }
      throw new Error(errorDetails);
    }
    useAppStore.getState().setIsBackendConnected(true);
    return response;
  } catch (error) {
    console.error(`Error calling createSpace API for space ${spaceId}:`, error);
    useAppStore.getState().setIsBackendConnected(false);
    throw error;
  }
}

/**
 * Deletes a space.
 * @param spaceId The ID of the space to delete.
 * @returns A promise that resolves when the space is deleted.
 */
export async function deleteSpace(spaceId: string): Promise<void> {
  try {
    const response = await fetch(`${API_BASE_URL}/spaces/${spaceId}`, {
      method: "DELETE",
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore
      }
      throw new Error(errorDetails);
    }
    useAppStore.getState().setIsBackendConnected(true);
  } catch (error) {
    console.error(`Error calling deleteSpace API for space ${spaceId}:`, error);
    useAppStore.getState().setIsBackendConnected(false);
    throw error;
  }
}

// --- Types for Sign POD operation ---
export interface SignPodRequest {
  private_key: string;
  entries: { [key: string]: Value }; // Value is from @/types/pod2
}

// Response is a SignedPod object
export type SignPodResponse = SignedPod; // From @/types/pod2

/**
 * Signs a new POD with the given entries and private key.
 * @param payload The private key and entries for the POD.
 * @returns A promise that resolves to the signed POD data.
 */
export async function signPod(
  payload: SignPodRequest
): Promise<SignPodResponse> {
  try {
    const response = await fetch(`${API_BASE_URL}/pods/sign`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        Accept: "application/json",
      },
      body: JSON.stringify(payload),
    });

    if (!response.ok) {
      let errorDetails = `HTTP error! status: ${response.status}`;
      try {
        const errorData = await response.json();
        errorDetails =
          errorData.error || errorData.message || JSON.stringify(errorData);
      } catch (e) {
        // Ignore if error body is not JSON or empty
      }
      throw new Error(errorDetails);
    }

    const signedPodData: SignPodResponse = await response.json();
    useAppStore.getState().setIsBackendConnected(true);
    return signedPodData;
  } catch (error) {
    console.error("Error calling signPod API:", error);
    useAppStore.getState().setIsBackendConnected(false);
    throw error; // Re-throw for the caller to handle
  }
}
