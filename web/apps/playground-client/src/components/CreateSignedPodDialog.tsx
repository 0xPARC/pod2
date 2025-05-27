import React, { useState, useEffect } from "react";
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
  DialogDescription,
  DialogFooter,
  DialogClose,
} from "./ui/dialog";
import { Button } from "./ui/button";
import { Input } from "./ui/input";
import { Label } from "./ui/label";
import { ScrollArea } from "./ui/scroll-area";
import { PlusCircle, Trash2, X } from "lucide-react";
import type { Value, Dictionary, Set as PodSet, Array as PodArray } from "@/types/pod2";

// Define the structure for an entry in the UI
type ValueTypeName = "string" | "boolean" | "Int" | "Raw" | "Array" | "Set" | "Dictionary";

interface PodEntry {
  id: string; // Unique ID for React key
  keyName: string;
  valueType: ValueTypeName;
  value: any; // This will be structured based on valueType
  keyError?: string;
  keyInteracted?: boolean; // New field to track interaction
  // We might need value errors too, especially for complex types
}

interface CreateSignedPodDialogProps {
  isOpen: boolean;
  onOpenChange: (isOpen: boolean) => void;
  activeSpaceId: string | null;
  // onSignPod: (podData: SignedPodData) => void; // Callback when "Sign" is clicked with valid data
}

// Placeholder for the actual SignedPod data structure to be built
// interface SignedPodData {
//   entries: { [key: string]: Value };
//   // other fields like podType will be added
// }

const CreateSignedPodDialog: React.FC<CreateSignedPodDialogProps> = ({
  isOpen,
  onOpenChange,
  activeSpaceId,
}) => {
  const [entries, setEntries] = useState<PodEntry[]>([]);
  const [isFormValid, setIsFormValid] = useState(false);

  // Function to add a new blank entry
  const addEntry = () => {
    setEntries([
      ...entries,
      {
        id: crypto.randomUUID(),
        keyName: "",
        valueType: "string",
        value: "",
        keyInteracted: false,
      },
    ]);
  };

  const removeEntry = (id: string) => {
    setEntries(entries.filter((entry) => entry.id !== id));
  };

  const updateEntry = (id: string, updatedFields: Partial<PodEntry>) => {
    setEntries(
      entries.map((entry) =>
        entry.id === id ? { ...entry, ...updatedFields } : entry
      )
    );
  };

  // Effect to validate the form whenever entries change
  useEffect(() => {
    // Basic validation: at least one entry, all keys non-empty and unique
    if (entries.length === 0) {
      setIsFormValid(false);
      return;
    }
    const keys = new Set<string>();
    let allKeysValid = true;
    for (const entry of entries) {
      if (!entry.keyName.trim()) {
        allKeysValid = false;
        if (entry.keyInteracted && entry.keyError !== "Key cannot be empty.") { // Check for interaction
          updateEntry(entry.id, { keyError: "Key cannot be empty." });
        }
      } else if (keys.has(entry.keyName.trim())) {
        allKeysValid = false;
        if (entry.keyError !== "Key must be unique.") {
          updateEntry(entry.id, { keyError: "Key must be unique." });
        }
      } else {
        if (entry.keyError) {
          updateEntry(entry.id, { keyError: undefined });
        }
        keys.add(entry.keyName.trim());
      }
    }
    // TODO: Add validation for values based on type
    setIsFormValid(allKeysValid); // Placeholder, more complex validation needed
  }, [entries]);

  const handleSign = () => {
    if (!isFormValid) {
      // This should ideally not happen if button is disabled
      console.error("Attempted to sign with invalid form.");
      return;
    }
    // Construct the SignedPod.entries object
    const signedPodEntries: { [key: string]: Value } = {};
    entries.forEach(entry => {
      // TODO: Convert entry.value to the correct Value type based on entry.valueType
      // This is a placeholder and needs proper type conversion logic
      if (entry.keyName.trim()) {
        switch (entry.valueType) {
          case "string":
            signedPodEntries[entry.keyName.trim()] = entry.value as string;
            break;
          case "boolean":
            signedPodEntries[entry.keyName.trim()] = entry.value as boolean;
            break;
          case "Int":
            signedPodEntries[entry.keyName.trim()] = { Int: String(entry.value) };
            break;
          case "Raw":
            signedPodEntries[entry.keyName.trim()] = { Raw: String(entry.value) };
            break;
          // TODO: Handle Array, Set, Dictionary - this will be complex
          default:
            console.warn("Unsupported value type for entry:", entry);
        }
      }
    });
    console.log("Constructed Signed POD Entries:", signedPodEntries);
    // console.log("TODO: Call onSignPod with data", { entries: signedPodEntries, podType: "Signed" });
    // onOpenChange(false); // Close dialog on sign
  };

  const renderValueInput = (entry: PodEntry) => {
    // This will become much more complex for Array, Set, Dictionary
    switch (entry.valueType) {
      case "string":
      case "Int": // Int is string in UI, then converted
      case "Raw": // Raw is string in UI, then converted
        return (
          <Input
            type={entry.valueType === "Int" ? "number" : "text"}
            value={entry.value}
            onChange={(e) => updateEntry(entry.id, { value: e.target.value })}
            placeholder={`Enter ${entry.valueType} value`}
            className="flex-grow"
          />
        );
      case "boolean":
        return (
          <input
            type="checkbox"
            checked={!!entry.value}
            onChange={(e) => updateEntry(entry.id, { value: e.target.checked })}
            className="ml-2 h-5 w-5"
          />
        );
      // TODO: Implement Array, Set, Dictionary inputs
      case "Array":
        return <div className="text-sm text-gray-500 p-2 border rounded-md">Array input (TODO)</div>;
      case "Set":
        return <div className="text-sm text-gray-500 p-2 border rounded-md">Set input (TODO)</div>;
      case "Dictionary":
        return <div className="text-sm text-gray-500 p-2 border rounded-md">Dictionary input (TODO)</div>;
      default:
        return <Input value="Unsupported type" disabled />;
    }
  };


  return (
    <Dialog open={isOpen} onOpenChange={onOpenChange}>
      <DialogContent className="sm:max-w-3xl h-[80vh] max-h-[80vh] flex flex-col">
        <DialogHeader>
          <DialogTitle>Create New Signed POD</DialogTitle>
          <DialogDescription>
            Define the key-value entries for your new Signed POD in space: {activeSpaceId || "None"}.
            Keys must be unique and non-empty.
          </DialogDescription>
        </DialogHeader>

        <div className="flex-grow flex flex-col min-h-0 py-4">
          <div className="flex justify-between items-center mb-3">
            <Label className="text-lg font-semibold">Entries</Label>
            <Button variant="outline" size="sm" onClick={addEntry}>
              <PlusCircle className="mr-2 h-4 w-4" /> Add Entry
            </Button>
          </div>

          <ScrollArea className="flex-grow border rounded-md p-1 pr-3 max-h-[100%]">
            {entries.length === 0 ? (
              <p className="text-sm text-gray-500 text-center py-4">
                No entries added yet. Click "Add Entry" to start.
              </p>
            ) : (
              <div className="space-y-4">
                {entries.map((entry, index) => (
                  <div key={entry.id} className="p-3 border rounded-lg shadow-sm bg-background">
                    <div className="flex items-start space-x-3">
                      <div className="flex-grow space-y-2">
                        {/* Key and Type Row */}
                        <div className="flex space-x-3">
                          {/* Key Input */}
                          <div className="flex-grow flex flex-col gap-1 w-1/2">
                            <Label htmlFor={`key-${entry.id}`}>Key</Label>
                            <Input
                              id={`key-${entry.id}`}
                              value={entry.keyName}
                              onChange={(e) => updateEntry(entry.id, { keyName: e.target.value, keyError: undefined })}
                              onBlur={() => updateEntry(entry.id, { keyInteracted: true })} // Set interacted on blur
                              placeholder="Enter key (e.g., 'user_id')"
                              className={entry.keyError ? "border-red-500" : ""}
                            />
                            {entry.keyError && <p className="text-xs text-red-500 mt-1">{entry.keyError}</p>}
                          </div>

                          {/* Value Type Selector */}
                          <div className="flex-grow flex flex-col gap-1 w-1/2">
                            <Label htmlFor={`type-${entry.id}`}>Type</Label>
                            <select
                              id={`type-${entry.id}`}
                              value={entry.valueType}
                              onChange={(e) =>
                                updateEntry(entry.id, {
                                  valueType: e.target.value as ValueTypeName,
                                  // Reset value when type changes to avoid type mismatches
                                  value: e.target.value === "boolean" ? false : "",
                                })
                              }
                              className="w-full p-2 border rounded-md bg-background h-[calc(2.25rem+2px)]" // Match input height
                            >
                              <option value="string">String</option>
                              <option value="boolean">Boolean</option>
                              <option value="Int">Integer (Int64)</option>
                              <option value="Raw">Raw Bytes (Hex String)</option>
                              <option value="Array">Array</option>
                              <option value="Set">Set</option>
                              <option value="Dictionary">Dictionary</option>
                            </select>
                          </div>
                        </div>

                        {/* Value Input */}
                        <div className="flex flex-col gap-2 pt-2">
                          <Label htmlFor={`value-${entry.id}`}>Value</Label>
                          {renderValueInput(entry)}
                        </div>
                      </div>
                      <Button
                        variant="ghost"
                        size="icon"
                        onClick={() => removeEntry(entry.id)}
                        className="mt-1 text-gray-500 hover:text-red-600 flex-shrink-0"
                        title="Remove Entry"
                      >
                        <Trash2 className="h-4 w-4" />
                      </Button>
                    </div>
                  </div>
                ))}
              </div>
            )}
          </ScrollArea>
        </div>

        <DialogFooter className="mt-auto pt-4 border-t">
          <DialogClose asChild>
            <Button variant="outline">Cancel</Button>
          </DialogClose>
          <Button onClick={handleSign} disabled={!isFormValid}>
            Sign POD
          </Button>
        </DialogFooter>
      </DialogContent>
    </Dialog>
  );
};

export default CreateSignedPodDialog; 