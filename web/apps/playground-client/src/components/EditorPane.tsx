import React, { useEffect, useCallback, useRef, useState } from "react";
import Editor, { type OnChange, type Monaco, loader } from "@monaco-editor/react";
import * as monacoApi from "monaco-editor/esm/vs/editor/editor.api";
import { useAppStore } from "../lib/store";
import {
  validateCode,
  DiagnosticSeverity,
  type Diagnostic as ApiDiagnostic,
} from "../lib/backendServiceClient";
import { podlogMonarchLanguage } from "../lib/podlogMonarchLanguage";
import * as monaco from 'monaco-editor';
import { useTheme } from "./theme-provider";
import ControlsPane from "./ControlsPane";

loader.config({ monaco });

// Helper to convert API Diagnostic to Monaco MarkerData
const toMonacoMarker = (diag: ApiDiagnostic): monacoApi.editor.IMarkerData => {
  // Use monacoApi type
  let severity: monacoApi.MarkerSeverity; // Use monacoApi type
  switch (diag.severity) {
    case DiagnosticSeverity.Error:
      severity = monacoApi.MarkerSeverity.Error; // Use monacoApi type
      break;
    case DiagnosticSeverity.Warning:
      severity = monacoApi.MarkerSeverity.Warning; // Use monacoApi type
      break;
    case DiagnosticSeverity.Information:
      severity = monacoApi.MarkerSeverity.Info; // Use monacoApi type
      break;
    case DiagnosticSeverity.Hint:
      severity = monacoApi.MarkerSeverity.Hint; // Use monacoApi type
      break;
    default:
      severity = monacoApi.MarkerSeverity.Info; // Default // Use monacoApi type
  }
  return {
    message: diag.message,
    severity,
    startLineNumber: diag.start_line,
    startColumn: diag.start_column,
    endLineNumber: diag.end_line,
    endColumn: diag.end_column,
  };
};

const DEBOUNCE_DELAY_MS = 100;

const EditorPane: React.FC = () => {
  const fileContent = useAppStore((state) => state.fileContent);
  const setFileContent = useAppStore((state) => state.setFileContent);
  const saveToLocalForage = useAppStore((state) => state.saveToLocalForage);
  const editorDiagnostics = useAppStore((state) => state.editorDiagnostics);
  const setEditorDiagnostics = useAppStore(
    (state) => state.setEditorDiagnostics
  );
  const isStoreInitialized = useAppStore((state) => state.isStoreInitialized);

  const editorRef = useRef<monacoApi.editor.IStandaloneCodeEditor | null>(null);
  const monacoRef = useRef<Monaco | null>(null);
  const debounceTimeoutRef = useRef<number | null>(null);

  const { theme } = useTheme();

  const handleEditorChange: OnChange = (value) => {
    setFileContent(value || "");
  };

  const debouncedSaveAndValidate = useCallback(
    async (content: string) => {
      await saveToLocalForage();
      const validationResponse = await validateCode(content);
      // console.log('[EditorPane] Diagnostics from validateCode:', validationResponse.diagnostics);
      setEditorDiagnostics(validationResponse.diagnostics);
    },
    [saveToLocalForage, setEditorDiagnostics]
  );

  useEffect(() => {
    if (!isStoreInitialized || fileContent === undefined) {
      return;
    }
    if (debounceTimeoutRef.current) {
      clearTimeout(debounceTimeoutRef.current);
    }
    debounceTimeoutRef.current = window.setTimeout(() => {
      debouncedSaveAndValidate(fileContent);
    }, DEBOUNCE_DELAY_MS);
    return () => {
      if (debounceTimeoutRef.current) {
        clearTimeout(debounceTimeoutRef.current);
      }
    };
  }, [fileContent, isStoreInitialized, debouncedSaveAndValidate]);

  // Effect to update Monaco editor markers when editorDiagnostics change
  useEffect(() => {
    console.log(
      "[EditorPane] editorDiagnostics changed (dynamic):",
      editorDiagnostics
    );
    if (editorRef.current && monacoRef.current) {
      const model = editorRef.current.getModel();
      console.log(
        "[EditorPane] Editor and monaco instance available for dynamic markers. Model available:",
        !!model
      );
      if (model) {
        const markers = editorDiagnostics.map(toMonacoMarker);
        console.log("[EditorPane] Dynamic Monaco markers to set:", markers);
        monacoRef.current.editor.setModelMarkers(
          model,
          "podlog-validator",
          markers
        );
      } else {
        console.log("[EditorPane] Model not available for dynamic markers.");
      }
    } else {
      console.log(
        "[EditorPane] Editor or monaco instance not available for dynamic markers."
      );
    }
  }, [editorDiagnostics]); // Depends on editorDiagnostics, editorRef and monacoRef are stable

  function handleEditorDidMount(
    mountedEditor: monacoApi.editor.IStandaloneCodeEditor,
    mountedMonaco: Monaco
  ) {
    editorRef.current = mountedEditor;
    monacoRef.current = mountedMonaco;
    console.log("[EditorPane] Editor did mount.");

    mountedMonaco.languages.register({ id: "podlog" });
    mountedMonaco.languages.setMonarchTokensProvider(
      "podlog",
      podlogMonarchLanguage
    );
    console.log(
      "[EditorPane] Podlog language registered and Monarch tokens set."
    );
  }

  if (!isStoreInitialized) {
    // Optional loader
  }

  return (
    <div className="flex flex-col h-full">
      <ControlsPane />
      <div className="border-bg bg-gray-100 dark:bg-[#1e1e1e] h-full w-full px-1 py-2">
        <Editor
          height="100%"
          width="100%"
          language="podlog"
          theme={theme === "dark" ? "vs-dark" : theme === "system" && window.matchMedia("(prefers-color-scheme: dark)").matches ? "vs-dark" : "vs-light"}
          value={fileContent}
          onChange={handleEditorChange}
          onMount={handleEditorDidMount}
          options={{
            minimap: { enabled: false },
            fontSize: 14,
            wordWrap: "on",
            scrollBeyondLastLine: false,
            automaticLayout: true,
          }}
        />
      </div>
    </div>
  );
};

export default EditorPane;
