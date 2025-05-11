import { create } from 'zustand';
import localForage from 'localforage';

const PODLOG_MVP_FILE_KEY = 'podlogMvpFile';

// Define the state shape
interface AppState {
  fileContent: string;
  isLoadingExecution: boolean;
  executionResult: string | null; // Assuming JSON string or structured object later
  executionError: string | null;
  editorDiagnostics: any[]; // Replace 'any' with a more specific Diagnostic type later
  hasErrors: boolean; // Derived from editorDiagnostics
  isBackendConnected: boolean;
  isStoreInitialized: boolean; // To track if initial load is done
  // Actions
  setFileContent: (content: string) => void;
  setLoadingExecution: (isLoading: boolean) => void;
  setExecutionResult: (result: string | null) => void;
  setExecutionError: (error: string | null) => void;
  setEditorDiagnostics: (diagnostics: any[]) => void; // Replace 'any'
  setIsBackendConnected: (isConnected: boolean) => void;
  saveToLocalForage: () => Promise<void>;
  loadFromLocalForage: () => Promise<void>;
}

// Create the store
export const useAppStore = create<AppState>((set, get) => ({
  // Initial state
  fileContent: '', // Default to empty string for MVP
  isLoadingExecution: false,
  executionResult: null,
  executionError: null,
  editorDiagnostics: [],
  hasErrors: false, // Initial value, will be updated based on editorDiagnostics
  isBackendConnected: false, // Assume not connected initially
  isStoreInitialized: false,

  // Actions
  setFileContent: (content) => {
    set({ fileContent: content });
    // Auto-save removed from here, will be handled by debounced effect in EditorPane
    // get().saveToLocalForage(); 
  },
  setLoadingExecution: (isLoading) => set({ isLoadingExecution: isLoading }),
  setExecutionResult: (result) => set({ executionResult: result, executionError: null }), // Clear error on new result
  setExecutionError: (error) => set({ executionError: error, executionResult: null }), // Clear result on new error
  setEditorDiagnostics: (diagnostics) => set({
    editorDiagnostics: diagnostics,
    hasErrors: diagnostics.length > 0,
  }),
  setIsBackendConnected: (isConnected) => set({ isBackendConnected: isConnected }),

  saveToLocalForage: async () => {
    try {
      await localForage.setItem(PODLOG_MVP_FILE_KEY, get().fileContent);
      console.log('File content saved to localForage.');
    } catch (error) {
      console.error('Failed to save to localForage:', error);
    }
  },

  loadFromLocalForage: async () => {
    if (get().isStoreInitialized) return; // Prevent multiple initial loads
    try {
      const storedContent = await localForage.getItem<string>(PODLOG_MVP_FILE_KEY);
      if (storedContent !== null) {
        set({ fileContent: storedContent, isStoreInitialized: true });
        console.log('File content loaded from localForage.');
      } else {
        set({ fileContent: '// Welcome to the Podlog Playground!\n', isStoreInitialized: true }); // Default content if nothing stored
        console.log('No content in localForage, initialized with default.');
      }
    } catch (error) {
      console.error('Failed to load from localForage:', error);
      set({ fileContent: '// Error loading from localForage.\n', isStoreInitialized: true }); // Fallback content
    }
  },
}));

// Initialize by loading from localForage when the app starts
// This is a side effect that runs when this module is imported.
useAppStore.getState().loadFromLocalForage();

// Example of a selector to get derived state (optional, can also be done in components)
// export const selectHasErrors = (state: AppState) => state.editorDiagnostics.length > 0; 