import React from 'react';
import Ajv, { type ValidateFunction, type Schema } from 'ajv/dist/2019';
import { useAppStore } from '../lib/store';
import PodCard from './PodCard'; // Assuming PodCard.tsx is in the same directory
import type { MainPod } from '../types/pod2';
import fullSchema from '../schemas.json'; // Import the full schema

// --- AJV Setup ---
// Make AJV less strict about unknown formats like "uint"
const ajv = new Ajv({ allErrors: true, strict: false });

let validateMainPod: ValidateFunction<MainPod> | ((data: any) => data is MainPod);

try {
  // Compile the entire schema. AJV will process all definitions.
  // No need to add fullSchema separately with addSchema if we compile it directly.
  ajv.compile(fullSchema);

  // Get the specific validator for MainPodHelper using its path within the full schema.
  const specificValidator = ajv.getSchema<MainPod>('#/definitions/MainPodHelper');

  if (specificValidator) {
    validateMainPod = specificValidator;
    console.log('MainPod schema validator obtained successfully via getSchema.');
  } else {
    // This case should ideally not be hit if the schema path is correct
    // and MainPodHelper is defined in fullSchema.definitions.
    throw new Error('Could not get validator for #/definitions/MainPodHelper from compiled schema.');
  }
} catch (e) {
  console.error("Failed to compile full schema or get MainPod validator:", e);
  // Fallback validator if compilation or getSchema fails
  validateMainPod = (data: any): data is MainPod => {
    console.warn("AJV setup failed, using basic type guard for MainPod.");
    return !!(data &&
      typeof data.podClass === 'string' &&
      typeof data.podType === 'string' &&
      typeof data.proof === 'string' &&
      Array.isArray(data.publicStatements));
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

  let content;

  if (isLoadingExecution) {
    content = <p className="p-4 text-gray-500 dark:text-gray-400">Executing...</p>;
  } else if (executionError) {
    content = <pre className="p-4 text-sm text-red-600 dark:text-red-400 whitespace-pre-wrap break-all">Error: {executionError}</pre>;
  } else if (executionResult) {
    try {
      const parsedResult = JSON.parse(executionResult);
      if (isMainPod(parsedResult)) {
        content = <PodCard pod={parsedResult} />;
      } else {
        // If it's not a MainPod or something else, display as string
        content = <pre className="p-4 text-sm whitespace-pre-wrap break-all">{executionResult}</pre>;
      }
    } catch (e) {
      // If parsing fails, it's likely not JSON or not the JSON we expect for a POD
      console.warn("Failed to parse execution result as JSON for PodCard, displaying as raw string:", e);
      content = <pre className="p-4 text-sm whitespace-pre-wrap break-all">{executionResult}</pre>;
    }
  } else {
    content = <p className="p-4 text-gray-500 dark:text-gray-400">Execution results will appear here.</p>;
  }

  return (
    <div className="w-full h-full bg-white dark:bg-gray-800 border border-gray-300 dark:border-gray-600 rounded overflow-auto p-1">
      {content}
    </div>
  );
};

export default ResultsPane; 