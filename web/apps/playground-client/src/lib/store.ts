import { create } from "zustand";
import localForage from "localforage";
import type { PodInfo } from "@/types/pod2";

const PODLOG_MVP_FILE_KEY = "podlogMvpFile";
const ACTIVE_SPACE_ID_KEY = "activeSpaceId";

// Define the state shape
export type MainAreaTab = "editor" | "podViewer";

interface AppState {
  fileContent: string;
  isLoadingExecution: boolean;
  executionResult: string | null; // Assuming JSON string or structured object later
  executionError: string | null;
  editorDiagnostics: any[]; // Replace 'any' with a more specific Diagnostic type later
  hasErrors: boolean; // Derived from editorDiagnostics
  isBackendConnected: boolean;
  isStoreInitialized: boolean; // To track if initial load is done
  activeSpaceId: string | null;
  // --- IDE Layout State ---
  isExplorerCollapsed: boolean;
  isResultsPaneOpen: boolean;
  resultsPaneSize: number; // Percentage
  // Actions
  setFileContent: (content: string) => void;
  setLoadingExecution: (isLoading: boolean) => void;
  setExecutionResult: (result: string | null) => void;
  setExecutionError: (error: string | null) => void;
  setEditorDiagnostics: (diagnostics: any[]) => void; // Replace 'any'
  setIsBackendConnected: (isConnected: boolean) => void;
  setActiveSpaceId: (spaceId: string | null) => void;
  // --- IDE Layout Actions ---
  toggleExplorer: () => void;
  setIsResultsPaneOpen: (isOpen: boolean) => void;
  setResultsPaneSize: (size: number) => void;
  saveToLocalForage: () => Promise<void>;
  loadFromLocalForage: () => Promise<void>;

  // --- Main Area Tab State & Actions ---
  activeMainAreaTab: MainAreaTab;
  selectedPodForViewing: PodInfo | null; // Using PodInfo from backendServiceClient
  setActiveMainAreaTab: (tab: MainAreaTab) => void;
  setSelectedPodForViewing: (pod: PodInfo | null) => void;
}

// Create the store
export const useAppStore = create<AppState>((set, get) => ({
  // Initial state
  fileContent: "", // Default to empty string for MVP
  isLoadingExecution: false,
  executionResult: null,
  executionError: null,
  editorDiagnostics: [],
  hasErrors: false, // Initial value, will be updated based on editorDiagnostics
  isBackendConnected: false, // Assume not connected initially
  isStoreInitialized: false,
  activeSpaceId: null,
  // --- IDE Layout State ---
  isExplorerCollapsed: false,
  isResultsPaneOpen: false, // Default to closed
  resultsPaneSize: 33, // Default to 33% height

  // Actions
  setFileContent: (content) => {
    set({ fileContent: content });
    // Auto-save removed from here, will be handled by debounced effect in EditorPane
    // get().saveToLocalForage();
  },
  setLoadingExecution: (isLoading) => set({ isLoadingExecution: isLoading }),
  setExecutionResult: (result) =>
    set({ executionResult: result, executionError: null }), // Clear error on new result
  setExecutionError: (error) =>
    set({ executionError: error, executionResult: null }), // Clear result on new error
  setEditorDiagnostics: (diagnostics) =>
    set({
      editorDiagnostics: diagnostics,
      hasErrors: diagnostics.length > 0,
    }),
  setIsBackendConnected: (isConnected) =>
    set({ isBackendConnected: isConnected }),
  setActiveSpaceId: (spaceId) => {
    set({ activeSpaceId: spaceId });
    get().saveToLocalForage(); // Persist on change
  },

  // --- IDE Layout Actions ---
  toggleExplorer: () =>
    set((state) => ({ isExplorerCollapsed: !state.isExplorerCollapsed })),
  setIsResultsPaneOpen: (isOpen) => set({ isResultsPaneOpen: isOpen }),
  setResultsPaneSize: (size) => set({ resultsPaneSize: size }),

  saveToLocalForage: async () => {
    try {
      await localForage.setItem(PODLOG_MVP_FILE_KEY, get().fileContent);
      await localForage.setItem(ACTIVE_SPACE_ID_KEY, get().activeSpaceId);
      console.log("File content and active space ID saved to localForage.");
    } catch (error) {
      console.error("Failed to save to localForage:", error);
    }
  },

  loadFromLocalForage: async () => {
    if (get().isStoreInitialized) return; // Prevent multiple initial loads
    try {
      const storedContent =
        await localForage.getItem<string>(PODLOG_MVP_FILE_KEY);
      const storedActiveSpaceId = await localForage.getItem<string | null>(
        ACTIVE_SPACE_ID_KEY
      );

      let fileContentToSet = "// Welcome to the POD Playground!\n";
      if (storedContent !== null) {
        fileContentToSet = storedContent;
        console.log("File content loaded from localForage.");
      } else {
        console.log(
          "No file content in localForage, initialized with default."
        );
      }

      set({
        fileContent: fileContentToSet,
        activeSpaceId: storedActiveSpaceId,
        isStoreInitialized: true,
      });
      if (storedActiveSpaceId !== null) {
        console.log("Active space ID loaded from localForage.");
      } else {
        console.log("No active space ID in localForage, initialized to null.");
      }
    } catch (error) {
      console.error("Failed to load from localForage:", error);
      set({
        fileContent: "// Error loading file content from localForage.\n",
        activeSpaceId: null, // Fallback for activeSpaceId on error
        isStoreInitialized: true,
      }); // Fallback content
    }
  },

  // --- Main Area Tab State & Actions ---
  activeMainAreaTab: "editor", // Default to editor tab
  selectedPodForViewing: null,
  setActiveMainAreaTab: (tab) => set({ activeMainAreaTab: tab }),
  setSelectedPodForViewing: (pod) => set({ selectedPodForViewing: pod }),
}));

// Initialize by loading from localForage when the app starts
// This is a side effect that runs when this module is imported.
useAppStore.getState().loadFromLocalForage();

// Example of a selector to get derived state (optional, can also be done in components)
// export const selectHasErrors = (state: AppState) => state.editorDiagnostics.length > 0;
