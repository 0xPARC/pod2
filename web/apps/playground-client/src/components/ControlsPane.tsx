import React from "react";
import { useAppStore } from "../lib/store";
import { executeCode } from "../lib/backendServiceClient";

// Basic SVG Icon Components
const GreenCheckIcon: React.FC<{ className?: string }> = ({ className }) => (
  <svg
    className={className}
    xmlns="http://www.w3.org/2000/svg"
    fill="none"
    viewBox="0 0 24 24"
    strokeWidth={1.5}
    stroke="currentColor"
  >
    <path
      strokeLinecap="round"
      strokeLinejoin="round"
      d="M9 12.75 11.25 15 15 9.75M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0Z"
    />
  </svg>
);

const RedCrossIcon: React.FC<{ className?: string }> = ({ className }) => (
  <svg
    className={className}
    xmlns="http://www.w3.org/2000/svg"
    fill="none"
    viewBox="0 0 24 24"
    strokeWidth={1.5}
    stroke="currentColor"
  >
    <path
      strokeLinecap="round"
      strokeLinejoin="round"
      d="m9.75 9.75 4.5 4.5m0-4.5-4.5 4.5M21 12a9 9 0 1 1-18 0 9 9 0 0 1 18 0Z"
    />
  </svg>
);

const ControlsPane: React.FC = () => {
  const fileContent = useAppStore((state) => state.fileContent);
  const hasErrors = useAppStore((state) => state.hasErrors);
  const editorDiagnostics = useAppStore((state) => state.editorDiagnostics);
  const isLoadingExecution = useAppStore((state) => state.isLoadingExecution);
  const setLoadingExecution = useAppStore((state) => state.setLoadingExecution);
  const setExecutionResult = useAppStore((state) => state.setExecutionResult);
  const setExecutionError = useAppStore((state) => state.setExecutionError);
  const setIsResultsPaneOpen = useAppStore((state) => state.setIsResultsPaneOpen);
  const activeSpaceId = useAppStore((state) => state.activeSpaceId);

  const handleExecute = async () => {
    if (hasErrors) {
      console.warn("Cannot execute code with errors.");
      return;
    }
    setLoadingExecution(true);
    setExecutionError(null);
    setExecutionResult(null);
    try {
      const result = await executeCode(fileContent, activeSpaceId ?? "");
      setExecutionResult(JSON.stringify(result, null, 2));
    } catch (error) {
      if (error instanceof Error) {
        setExecutionError(error.message);
      } else {
        setExecutionError("An unknown error occurred during execution.");
      }
    }
    setLoadingExecution(false);
    setIsResultsPaneOpen(true);
  };

  let errorDisplayMessage = "Code has errors";
  let fullErrorMessageForTooltip = "Code has errors";

  if (hasErrors && editorDiagnostics.length > 0) {
    const firstError = editorDiagnostics[0];
    // Ensure properties exist, though our Diagnostic type implies they do
    const line = firstError.start_line;
    const col = firstError.start_column;
    const msg = firstError.message;
    errorDisplayMessage = `L${line}:${col}: ${msg}`;
    fullErrorMessageForTooltip = `Line ${line}, Column ${col}: ${msg}`;
  }

  return (
    <div className="flex items-center justify-between bg-gray-200 dark:bg-gray-800">
      <div className="p-2 bg-gray-200 dark:bg-gray-800 flex items-center space-x-4">
        <button
          onClick={handleExecute}
          disabled={hasErrors || isLoadingExecution}
          className={`text-sm px-4 py-2 rounded font-semibold flex items-center justify-center
                    ${hasErrors || isLoadingExecution
              ? "bg-gray-400 dark:bg-gray-600 text-gray-600 dark:text-gray-400 cursor-not-allowed"
              : "bg-blue-500 hover:bg-blue-600 text-white"
            }
                  `}
        >
          {isLoadingExecution ? "Executing..." : "Execute"}
        </button>

        {!isLoadingExecution &&
          (hasErrors ? (
            <div
              title={fullErrorMessageForTooltip}
              className="flex items-center space-x-1"
            >
              <RedCrossIcon className="h-6 w-6 text-red-500 dark:text-red-400 flex-shrink-0" />
              <span
                className="text-sm text-red-600 dark:text-red-400 truncate max-w-md"
                title={fullErrorMessageForTooltip}
              >
                {errorDisplayMessage}
              </span>
            </div>
          ) : (
            <div title="Code is valid" className="flex items-center space-x-1">
              <GreenCheckIcon className="h-6 w-6 text-green-500 dark:text-green-400 flex-shrink-0" />
              <span className="text-sm text-green-600 dark:text-green-400">
                Code is valid
              </span>
            </div>
          ))}
      </div>
    </div >
  );
};

export default ControlsPane;
