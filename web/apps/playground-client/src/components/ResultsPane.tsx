import React, { useState } from "react";
import Ajv, { type ValidateFunction } from "ajv/dist/2019";
import { useAppStore } from "../lib/store";
import MainPodCard from "./MainPodCard";
import type { MainPod } from "@/types/pod2";
import fullSchema from "@/schemas.json"; // Import the full schema
import AddToSpaceDialog from "./AddToSpaceDialog"; // Import the dialog
import { Button } from "./ui/button"; // Import Button for "Add to Space"
import { PlusCircle } from "lucide-react"; // Icon for the button
import { MermaidDiagram } from "@lightenna/react-mermaid-diagram";

// --- AJV Setup ---
// Make AJV less strict about unknown formats like "uint"
const ajv = new Ajv({ allErrors: true, strict: false });

let validateMainPod:
  | ValidateFunction<MainPod>
  | ((data: any) => data is MainPod);

try {
  // Compile the entire schema. AJV will process all definitions.
  // No need to add fullSchema separately with addSchema if we compile it directly.
  ajv.compile(fullSchema);

  // Get the specific validator for MainPodHelper using its path within the full schema.
  const specificValidator = ajv.getSchema<MainPod>(
    "#/definitions/MainPod"
  );

  if (specificValidator) {
    validateMainPod = specificValidator;
    console.log(
      "MainPod schema validator obtained successfully via getSchema."
    );
  } else {
    // This case should ideally not be hit if the schema path is correct
    // and MainPodHelper is defined in fullSchema.definitions.
    throw new Error(
      "Could not get validator for #/definitions/MainPod from compiled schema."
    );
  }
} catch (e) {
  console.error("Failed to compile full schema or get MainPod validator:", e);
  // Fallback validator if compilation or getSchema fails
  validateMainPod = (data: any): data is MainPod => {
    console.warn("AJV setup failed, using basic type guard for MainPod.");
    return !!(
      data &&
      typeof data.podClass === "string" &&
      typeof data.podType === "string" &&
      typeof data.proof === "string" &&
      Array.isArray(data.publicStatements)
    );
  };
}

// Updated type guard using AJV
function isMainPod(obj: any): obj is MainPod {
  if (validateMainPod(obj)) {
    return true;
  }
  // console.log('AJV validation errors:', validateMainPod.errors); // Optional: for debugging
  return false;
}

const ResultsPane: React.FC = () => {
  const isLoadingExecution = useAppStore((state) => state.isLoadingExecution);
  const executionResult = useAppStore((state) => state.executionResult);
  const executionError = useAppStore((state) => state.executionError);
  const activeSpaceId = useAppStore((state) => state.activeSpaceId); // Get activeSpaceId

  // State for the dialog
  const [isAddToSpaceDialogOpen, setIsAddToSpaceDialogOpen] = useState(false);
  const [podForModal, setPodForModal] = useState<MainPod | null>(null);

  const handleOpenAddToSpaceDialog = (pod: MainPod) => {
    setPodForModal(pod);
    setIsAddToSpaceDialogOpen(true);
  };

  let content;

  if (isLoadingExecution) {
    content = (
      <p className="p-4 text-gray-500 dark:text-gray-400">Executing...</p>
    );
  } else if (executionError) {
    content = (
      <pre className="p-4 text-sm text-red-600 dark:text-red-400 whitespace-pre-wrap break-all">
        Error: {executionError}
      </pre>
    );
  } else if (executionResult) {
    try {
      const parsedResult = JSON.parse(executionResult);
      if (isMainPod(parsedResult.main_pod)) {
        // If it's a MainPod, display MainPodCard and an "Add to Space" button
        content = (
          <div className="p-2 space-y-2">
            <MainPodCard mainPod={parsedResult.main_pod} />
            <Button
              onClick={() => handleOpenAddToSpaceDialog(parsedResult.main_pod)}
              variant="outline"
              size="sm"
              className="mt-2 w-full flex items-center justify-center"
            >
              <PlusCircle className="mr-2 h-4 w-4" />
              Add to Space
            </Button>
            <div className="bg-gray-300 dark:bg-gray-400 p-1">
              <h3 className="text-sm font-bold">Proof</h3>
              <MermaidDiagram>{parsedResult.diagram}</MermaidDiagram>
            </div>
          </div>
        );
      } else {
        // If it's not a MainPod or something else, display as string
        content = (
          <pre className="p-4 text-sm whitespace-pre-wrap break-all">
            {executionResult}
          </pre>
        );
      }
    } catch (e) {
      // If parsing fails, it's likely not JSON or not the JSON we expect for a POD
      console.warn(
        "Failed to parse execution result as JSON for PodCard, displaying as raw string:",
        e
      );
      content = (
        <pre className="p-4 text-sm whitespace-pre-wrap break-all">
          {executionResult}
        </pre>
      );
    }
  } else {
    content = (
      <p className="p-4 text-gray-500 dark:text-gray-400 text-sm">
        Execution results will appear here.
      </p>
    );
  }

  return (
    <div className="w-full h-full bg-gray-200 dark:bg-gray-800 border border-gray-300 dark:border-gray-600 rounded overflow-auto p-1">
      {content}
      {podForModal && (
        <AddToSpaceDialog
          isOpen={isAddToSpaceDialogOpen}
          onOpenChange={setIsAddToSpaceDialogOpen}
          mainPodToSave={podForModal}
          defaultSpaceId={activeSpaceId}
        />
      )}
    </div>
  );
};

export default ResultsPane;
