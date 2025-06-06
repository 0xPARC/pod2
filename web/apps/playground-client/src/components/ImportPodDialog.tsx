import React, { useState, useEffect } from "react";
import { useQueryClient, useMutation } from "@tanstack/react-query";
import Ajv, { type ValidateFunction } from "ajv/dist/2019";
import { importPodDataToSpace, type ImportPodClientPayload } from "@/lib/backendServiceClient";
import { podKeys } from "@/hooks/useSpaceData";
import type { MainPod, SignedPod } from "@/types/pod2";
import fullSchema from "@/schemas.json";
import { Button } from "@/components/ui/button";
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
  DialogDescription,
  DialogFooter,
  DialogClose,
} from "@/components/ui/dialog";
import { Textarea } from "./ui/textarea";
import { Input } from "@/components/ui/input";
import { Label } from "@/components/ui/label";
import { toast } from "sonner";
import { AlertCircle, CheckCircle2 } from "lucide-react";

// --- AJV Setup ---
const ajv = new Ajv({ allErrors: true, strict: false });
let validateMainPod: ValidateFunction<MainPod> | ((data: any) => data is MainPod);
let validateSignedPod: ValidateFunction<Omit<SignedPod, 'id' | 'verify'>> | ((data: any) => data is Omit<SignedPod, 'id' | 'verify'>);

// Flag to indicate if AJV setup was successful for detailed error reporting
let ajvSuccessfullySetup = false;

try {
  ajv.compile(fullSchema);
  const mainPodValidator = ajv.getSchema<MainPod>("#/definitions/MainPod");
  const signedPodValidator = ajv.getSchema<Omit<SignedPod, 'id' | 'verify'>>("#/definitions/SignedPod");

  if (mainPodValidator) {
    validateMainPod = mainPodValidator;
  } else {
    throw new Error("Could not get validator for MainPod");
  }
  if (signedPodValidator) {
    validateSignedPod = signedPodValidator;
  } else {
    throw new Error("Could not get validator for SignedPod");
  }
  ajvSuccessfullySetup = true; // Mark AJV as successfully set up
} catch (e) {
  console.error("Failed to compile AJV schemas:", e);
  ajvSuccessfullySetup = false;
  validateMainPod = (data: any): data is MainPod => {
    console.warn("AJV MainPod setup failed, using basic type guard.");
    return !!(data && data.publicStatements && data.proof && data.podClass && data.podType);
  };
  validateSignedPod = (data: any): data is Omit<SignedPod, 'id' | 'verify'> => {
    console.warn("AJV SignedPod setup failed, using basic type guard.");
    return !!(data && data.entries && data.proof && data.podClass && data.podType);
  };
}

interface ImportPodDialogProps {
  isOpen: boolean;
  onOpenChange: (isOpen: boolean) => void;
  activeSpaceId: string | null;
}

const ImportPodDialog: React.FC<ImportPodDialogProps> = ({ isOpen, onOpenChange, activeSpaceId }) => {
  const [jsonInput, setJsonInput] = useState("");
  const [label, setLabel] = useState("");
  const [parsedPod, setParsedPod] = useState<MainPod | Omit<SignedPod, 'id' | 'verify'> | null>(null);
  const [podType, setPodType] = useState<"main" | "signed" | null>(null);
  const [validationError, setValidationError] = useState<string | null>(null);
  const [isJsonValid, setIsJsonValid] = useState<boolean | null>(null);

  const queryClient = useQueryClient();

  useEffect(() => {
    if (!jsonInput) {
      setParsedPod(null);
      setPodType(null);
      setValidationError(null);
      setIsJsonValid(null);
      return;
    }
    try {
      const parsed = JSON.parse(jsonInput);
      let mainPodValid = false;
      let signedPodValid = false;

      // It's important to call both validators to get their error states if using ajv.errors
      mainPodValid = validateMainPod(parsed);
      const mainPodErrors = ajvSuccessfullySetup && ajv.errors ? JSON.stringify(ajv.errors, null, 2) : "Invalid MainPod structure.";
      ajv.errors = null; // Clear errors before next validation

      signedPodValid = validateSignedPod(parsed);
      const signedPodErrors = ajvSuccessfullySetup && ajv.errors ? JSON.stringify(ajv.errors, null, 2) : "Invalid SignedPod structure.";
      ajv.errors = null; // Clear errors

      if (mainPodValid) {
        setParsedPod(parsed as MainPod);
        setPodType("main");
        setValidationError(null);
        setIsJsonValid(true);
      } else if (signedPodValid) {
        setParsedPod(parsed as Omit<SignedPod, 'id' | 'verify'>);
        setPodType("signed");
        setValidationError(null);
        setIsJsonValid(true);
      } else {
        setParsedPod(null);
        setPodType(null);
        setValidationError(`Not a valid MainPod or SignedPod.\nMainPod errors: ${mainPodErrors}\nSignedPod errors: ${signedPodErrors}`);
        setIsJsonValid(false);
      }
    } catch (e) {
      setParsedPod(null);
      setPodType(null);
      setValidationError("Invalid JSON format.");
      setIsJsonValid(false);
    }
  }, [jsonInput]);

  const importMutation = useMutation({
    mutationFn: (payload: ImportPodClientPayload) => {
      if (!activeSpaceId) throw new Error("Active space ID is null");
      return importPodDataToSpace(activeSpaceId, payload);
    },
    onSuccess: (data) => {
      toast.success(`POD "${data.label || data.id}" imported successfully into space "${activeSpaceId}".`);
      queryClient.invalidateQueries({ queryKey: podKeys.inSpace(activeSpaceId) });
      onOpenChange(false);
      setJsonInput("");
      setLabel("");
    },
    onError: (err) => {
      toast.error(`Failed to import POD: ${err instanceof Error ? err.message : String(err)}`);
    },
  });

  const handleSubmit = () => {
    if (!parsedPod || !podType || !activeSpaceId) {
      toast.error("Cannot submit: POD data, type, or active space is missing.");
      return;
    }

    importMutation.mutate({
      podType: podType,
      data: parsedPod,
      label: label.trim() || undefined,
    });
  };

  useEffect(() => {
    if (!isOpen) {
      setJsonInput("");
      setLabel("");
      setParsedPod(null);
      setPodType(null);
      setValidationError(null);
      setIsJsonValid(null);
    }
  }, [isOpen]);

  return (
    <Dialog open={isOpen} onOpenChange={onOpenChange}>
      <DialogContent className="sm:max-w-[600px]">
        <DialogHeader>
          <DialogTitle>Import POD to {activeSpaceId || "Space"}</DialogTitle>
          <DialogDescription>
            Paste the JSON representation of a MainPod or SignedPod. Pod Class will be derived. Label is optional.
          </DialogDescription>
        </DialogHeader>
        <div className="grid gap-4 py-4">
          <div className="grid gap-2">
            <Label htmlFor="pod-json">POD JSON</Label>
            <Textarea
              id="pod-json"
              placeholder='{"podClass": "MyPodClass", "podType": "ExampleType", "publicStatements": [], "proof": "0x..."}'
              value={jsonInput}
              onChange={(e: React.ChangeEvent<HTMLTextAreaElement>) => setJsonInput(e.target.value)}
              rows={8}
              className="min-h-[150px] max-h-[300px] font-mono text-xs overflow-scroll"
            />
            {isJsonValid === true && (
              <div className="flex items-center text-xs text-green-600 dark:text-green-500 mt-1">
                <CheckCircle2 className="h-4 w-4 mr-1" /> Valid {podType} JSON detected.
              </div>
            )}
            {isJsonValid === false && validationError && (
              <div className="flex items-center text-xs text-red-600 dark:text-red-500 mt-1">
                <AlertCircle className="h-4 w-4 mr-1 flex-shrink-0" /> {validationError.split('\n').map((line, i) => <div key={i}>{line}</div>)}
              </div>
            )}
          </div>
          <div className="grid grid-cols-1 gap-4">
            <div className="grid gap-2">
              <Label htmlFor="pod-label">Label (Optional)</Label>
              <Input
                id="pod-label"
                value={label}
                onChange={(e: React.ChangeEvent<HTMLInputElement>) => setLabel(e.target.value)}
                placeholder="e.g., Alice's Valid ID"
              />
            </div>
          </div>
        </div>
        <DialogFooter>
          <DialogClose asChild>
            <Button variant="outline">Cancel</Button>
          </DialogClose>
          <Button onClick={handleSubmit} disabled={!isJsonValid || importMutation.isPending}>
            {importMutation.isPending ? "Importing..." : "Import POD"}
          </Button>
        </DialogFooter>
      </DialogContent>
    </Dialog>
  );
};

export default ImportPodDialog; 