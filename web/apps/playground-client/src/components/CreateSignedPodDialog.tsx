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
import { PlusCircle, Trash2 } from "lucide-react";
import type { Value, Dictionary } from "@/types/pod2";
import {
  signPod,
  type SignPodRequest,
  importPodDataToSpace,
  type ImportPodClientPayload,
} from "../lib/backendServiceClient";
import { toast } from "sonner";
import { useQueryClient } from "@tanstack/react-query";
import { podKeys } from "../hooks/useSpaceData";

// Define the structure for an entry in the UI
type ValueTypeName = "string" | "boolean" | "Int" | "Raw" | "Array" | "Set" | "Dictionary";

// Add a type for items within an array or set
interface PodCollectionItem {
  id: string;
  type: ValueTypeName;
  value: any;
}

// Add a type for items within a dictionary
interface PodDictionaryItem {
  id: string;
  key: string;
  type: ValueTypeName;
  value: any;
}

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

const CreateSignedPodDialog: React.FC<CreateSignedPodDialogProps> = ({
  isOpen,
  onOpenChange,
  activeSpaceId,
}) => {
  const [entries, setEntries] = useState<PodEntry[]>([]);
  const [isFormValid, setIsFormValid] = useState(false);
  const [privateKey, setPrivateKey] = useState("");
  const [privateKeyError, setPrivateKeyError] = useState<string | undefined>();
  const [privateKeyInteracted, setPrivateKeyInteracted] = useState(false);
  const [label, setLabel] = useState("");
  const queryClient = useQueryClient();

  // New helper function in CreateSignedPodDialog
  const convertUiValueToPodValue = (value: any, type: ValueTypeName): Value => {
    switch (type) {
      case 'string':
        return value as string;
      case 'boolean':
        if (typeof value === 'boolean') {
          return value;
        }
        // Attempt to parse common string representations, default to false
        const val = String(value).toLowerCase();
        return val === 'true' || val === '1';
      case 'Int':
        const num = Number(value);
        if (!Number.isInteger(num)) {
          throw new Error(`Invalid integer value: ${value}`);
        }
        return { Int: String(value) };
      case 'Raw':
        // Basic hex validation (optional, backend might do more)
        if (/^[0-9a-fA-F]*$/.test(value)) {
          return { Raw: String(value) };
        } else {
          throw new Error(`Invalid hex string for Raw value: ${value}`);
        }
      case 'Array':
        if (!Array.isArray(value)) {
          throw new Error(`Value for Array is not a list`);
        }
        return { array: value.map((item: PodCollectionItem) => convertUiValueToPodValue(item.value, item.type)), max_depth: 32 };

      case 'Set':
        if (!Array.isArray(value)) {
          throw new Error(`Value for Set is not a list`);
        }
        const setValues = value.map((item: PodCollectionItem) => convertUiValueToPodValue(item.value, item.type));

        // Client-side uniqueness check for primitives.
        // Note: This is a shallow check and won't work for nested objects.
        // A more robust solution would involve deep equality checks or serialization.
        const seen = new Set();
        for (const v of setValues) {
          const key = typeof v === 'object' ? JSON.stringify(v) : v;
          if (seen.has(key)) {
            throw new Error(`Duplicate value found in Set: '${JSON.stringify(v)}'. Sets must contain unique values.`);
          }
          seen.add(key);
        }

        return { set: setValues, max_depth: 32 };

      case 'Dictionary':
        if (!Array.isArray(value)) {
          throw new Error(`Value for Dictionary is not a list of key-value pairs`);
        }
        const dict: Dictionary = { kvs: {}, max_depth: 32 };
        const keys = new Set<string>();
        for (const item of value as PodDictionaryItem[]) {
          const key = item.key.trim();
          if (!key) {
            throw new Error('Dictionary key cannot be empty.');
          }
          if (keys.has(key)) {
            throw new Error(`Duplicate key in Dictionary: '${key}'`);
          }
          keys.add(key);
          dict.kvs[key] = convertUiValueToPodValue(item.value, item.type);
        }
        return { Dictionary: dict };

      default:
        throw new Error(`Unsupported value type: ${type}`);
    }
  };

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
    let allEntriesValid = true;
    if (entries.length > 0) {
      const keys = new Set<string>();
      for (const entry of entries) {
        if (!entry.keyName.trim()) {
          allEntriesValid = false;
          if (entry.keyInteracted && entry.keyError !== "Key cannot be empty.") {
            updateEntry(entry.id, { keyError: "Key cannot be empty." });
          }
        } else if (keys.has(entry.keyName.trim())) {
          allEntriesValid = false;
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
    } else {
      allEntriesValid = false; // No entries, form not valid for submission
    }

    // Validate private key
    let pkValid = true;
    if (!privateKey.trim()) {
      pkValid = false;
      if (privateKeyInteracted) {
        setPrivateKeyError("Private key cannot be empty.");
      } else {
        setPrivateKeyError(undefined);
      }
    } else {
      setPrivateKeyError(undefined);
    }

    // TODO: Add validation for values based on type
    setIsFormValid(allEntriesValid && pkValid && entries.length > 0);
  }, [entries, privateKey, privateKeyInteracted]);

  const handleSign = async () => {
    if (!isFormValid) {
      toast.error("Form is not valid. Please check errors.");
      return;
    }
    // Construct the SignedPod.entries object
    const signedPodEntries: { [key: string]: Value } = {};
    let conversionError = false;

    entries.forEach(entry => {
      if (conversionError) return;
      if (entry.keyName.trim()) {
        try {
          const podValue = convertUiValueToPodValue(entry.value, entry.valueType);
          signedPodEntries[entry.keyName.trim()] = podValue;
        } catch (e) {
          toast.error(`Error processing entry '${entry.keyName}': ${(e as Error).message}`);
          conversionError = true;
          return;
        }
      }
    });

    if (conversionError) {
      toast.error("Failed to prepare POD entries due to conversion errors.");
      return;
    }

    if (Object.keys(signedPodEntries).length === 0 && entries.length > 0) {
      toast.error("No valid entries to sign after processing. Check for errors or unsupported types.");
      return;
    }
    if (entries.length === 0) {
      toast.error("Cannot sign an empty POD. Please add entries.");
      return;
    }

    const requestPayload: SignPodRequest = {
      private_key: privateKey.trim(),
      entries: signedPodEntries,
    };

    try {
      const signedPodData = await signPod(requestPayload);
      console.log("Successfully Signed POD:", signedPodData);

      // Now attempt to import the signed POD
      if (!activeSpaceId) {
        toast.error("No active space selected to import the POD into.");
        // Still close and reset form as signing was successful but import context is missing
        onOpenChange(false);
        setEntries([]);
        setPrivateKey("");
        setPrivateKeyInteracted(false);
        setPrivateKeyError(undefined);
        setLabel("");
        return;
      }

      try {
        const importPayload: ImportPodClientPayload = {
          podType: "signed",
          data: signedPodData, // The actual SignedPod object from signPod response
          // You might want to add a default label or let user specify one later
          // label: `Signed POD - ${new Date().toISOString()}` 
          label: label.trim() ? label.trim() : undefined,
        };
        const importedPodInfo = await importPodDataToSpace(activeSpaceId, importPayload);
        toast.success(`POD ${importedPodInfo.id.slice(0, 12)}... imported successfully into space ${activeSpaceId}!`);

        // Invalidate queries to refresh PodList
        queryClient.invalidateQueries({ queryKey: podKeys.inSpace(activeSpaceId) });

      } catch (importError) {
        console.error("Failed to import signed POD:", importError);
        toast.error(`Failed to import signed POD: ${(importError as Error).message}`);
        // Continue to close and reset, as signing itself was successful
      }

      onOpenChange(false); // Close dialog on successful sign & import attempt
      // Reset form state
      setEntries([]);
      setPrivateKey("");
      setPrivateKeyInteracted(false);
      setPrivateKeyError(undefined);
      setLabel("");
    } catch (error) {
      console.error("Failed to sign POD:", error);
      toast.error(`Failed to sign POD: ${(error as Error).message}`);
    }
  };

  const renderCollectionInput = (
    value: any,
    collectionType: 'Array' | 'Set',
    onChange: (newValue: any) => void,
    nestingLevel: number
  ) => {
    const items: PodCollectionItem[] = Array.isArray(value) ? value : [];

    const handleAddItem = () => {
      const newItem: PodCollectionItem = { id: crypto.randomUUID(), type: 'string', value: '' };
      onChange([...items, newItem]);
    };

    const handleRemoveItem = (itemId: string) => {
      onChange(items.filter(item => item.id !== itemId));
    };

    const handleUpdateItem = (itemId: string, updatedFields: Partial<PodCollectionItem>) => {
      const newItems = items.map(item => item.id === itemId ? { ...item, ...updatedFields } : item);
      onChange(newItems);
    };

    const handleUpdateItemType = (itemId: string, newType: ValueTypeName) => {
      let newValue: any = '';
      if (newType === 'boolean') newValue = false;
      if (newType === 'Array' || newType === 'Set' || newType === 'Dictionary') newValue = [];
      handleUpdateItem(itemId, { type: newType, value: newValue });
    };

    const renderItemValueInput = (item: PodCollectionItem, nestingLevel: number) => {
      switch (item.type) {
        case 'string':
        case 'Int':
        case 'Raw':
          return <Input type={item.type === 'Int' ? 'number' : 'text'} value={item.value} onChange={e => handleUpdateItem(item.id, { value: e.target.value })} placeholder={`Enter ${item.type} value`} className="flex-grow" />;
        case 'boolean':
          return <input type="checkbox" checked={!!item.value} onChange={e => handleUpdateItem(item.id, { value: e.target.checked })} className="ml-2 h-5 w-5" />;
        default: // Array, Set, Dictionary not supported as item types for now
          return <Input disabled value={`Type ${item.type} not supported in collections yet.`} className="bg-gray-100 dark:bg-gray-800" />;
      }
    };

    return (
      <div className="space-y-3 p-3 border rounded-md bg-gray-50 dark:bg-gray-800/50 ml-4">
        {items.map((item) => (
          <div key={item.id} className="flex items-start space-x-2 p-2 border rounded-md bg-background shadow-sm">
            <div className="flex-grow space-y-2">
              <div className="flex items-end space-x-2">
                <div className="flex-grow w-1/3">
                  <Label htmlFor={`item-type-${item.id}`} className="text-xs font-semibold">Item Type</Label>
                  <select
                    id={`item-type-${item.id}`}
                    value={item.type}
                    onChange={e => handleUpdateItemType(item.id, e.target.value as ValueTypeName)}
                    className="w-full p-2 border rounded-md bg-background h-10 text-sm"
                  >
                    <option value="string">String</option>
                    <option value="boolean">Boolean</option>
                    <option value="Int">Integer</option>
                    <option value="Raw">Raw (Hex)</option>
                    <option value="Array" disabled={nestingLevel >= 1}>Array</option>
                    <option value="Set" disabled={nestingLevel >= 1}>Set</option>
                    <option value="Dictionary" disabled={nestingLevel >= 1}>Dictionary</option>
                  </select>
                </div>
                <div className="flex-grow w-2/3">
                  <Label htmlFor={`item-value-${item.id}`} className="text-xs font-semibold">Item Value</Label>
                  {renderValueInput(item.value, item.type, (newValue) => handleUpdateItem(item.id, { value: newValue }), nestingLevel + 1)}
                </div>
              </div>
            </div>
            <Button variant="ghost" size="icon" onClick={() => handleRemoveItem(item.id)} className="mt-5 text-gray-500 hover:text-red-600 flex-shrink-0" title="Remove Item">
              <Trash2 className="h-4 w-4" />
            </Button>
          </div>
        ))}
        <Button variant="outline" size="sm" onClick={handleAddItem}>
          <PlusCircle className="mr-2 h-4 w-4" /> Add {collectionType} Item
        </Button>
      </div>
    );
  };

  const renderDictionaryInput = (
    value: any,
    onChange: (newValue: any) => void,
    nestingLevel: number
  ) => {
    const items: PodDictionaryItem[] = Array.isArray(value) ? value : [];

    const handleAddItem = () => {
      const newItem: PodDictionaryItem = { id: crypto.randomUUID(), key: '', type: 'string', value: '' };
      onChange([...items, newItem]);
    };

    const handleRemoveItem = (itemId: string) => {
      onChange(items.filter(item => item.id !== itemId));
    };

    const handleUpdateItem = (itemId: string, updatedFields: Partial<PodDictionaryItem>) => {
      const newItems = items.map(item => item.id === itemId ? { ...item, ...updatedFields } : item);
      onChange(newItems);
    };

    const handleUpdateItemType = (itemId: string, newType: ValueTypeName) => {
      let newValue: any = '';
      if (newType === 'boolean') newValue = false;
      if (newType === 'Array' || newType === 'Set' || newType === 'Dictionary') newValue = [];
      handleUpdateItem(itemId, { type: newType, value: newValue });
    };

    const renderItemValueInput = (item: PodDictionaryItem, nestingLevel: number) => {
      switch (item.type) {
        case 'string':
        case 'Int':
        case 'Raw':
          return <Input type={item.type === 'Int' ? 'number' : 'text'} value={item.value} onChange={e => handleUpdateItem(item.id, { value: e.target.value })} placeholder={`Enter ${item.type} value`} className="flex-grow" />;
        case 'boolean':
          return <input type="checkbox" checked={!!item.value} onChange={e => handleUpdateItem(item.id, { value: e.target.checked })} className="ml-2 h-5 w-5" />;
        default:
          return <Input disabled value={`Type ${item.type} not supported in collections yet.`} className="bg-gray-100 dark:bg-gray-800" />;
      }
    };

    return (
      <div className="space-y-3 p-3 border rounded-md bg-gray-50 dark:bg-gray-800/50 ml-4">
        {items.map((item) => (
          <div key={item.id} className="flex items-start space-x-2 p-2 border rounded-md bg-background shadow-sm">
            <div className="flex-grow space-y-2">
              <div className="flex items-end space-x-2">
                {/* Key Input */}
                <div className="flex-grow w-1/4">
                  <Label htmlFor={`dict-key-${item.id}`} className="text-xs font-semibold">Key</Label>
                  <Input id={`dict-key-${item.id}`} value={item.key} onChange={e => handleUpdateItem(item.id, { key: e.target.value })} placeholder="Enter key" />
                </div>
                {/* Type Selector */}
                <div className="flex-grow w-1/4">
                  <Label htmlFor={`dict-type-${item.id}`} className="text-xs font-semibold">Type</Label>
                  <select
                    id={`dict-type-${item.id}`}
                    value={item.type}
                    onChange={e => handleUpdateItemType(item.id, e.target.value as ValueTypeName)}
                    className="w-full p-2 border rounded-md bg-background h-10 text-sm"
                  >
                    <option value="string">String</option>
                    <option value="boolean">Boolean</option>
                    <option value="Int">Integer</option>
                    <option value="Raw">Raw (Hex)</option>
                    <option value="Array" disabled={nestingLevel >= 1}>Array</option>
                    <option value="Set" disabled={nestingLevel >= 1}>Set</option>
                    <option value="Dictionary" disabled={nestingLevel >= 1}>Dictionary</option>
                  </select>
                </div>
                {/* Value Input */}
                <div className="flex-grow w-2/4">
                  <Label htmlFor={`dict-value-${item.id}`} className="text-xs font-semibold">Value</Label>
                  {renderValueInput(item.value, item.type, (newValue) => handleUpdateItem(item.id, { value: newValue }), nestingLevel + 1)}
                </div>
              </div>
            </div>
            <Button variant="ghost" size="icon" onClick={() => handleRemoveItem(item.id)} className="mt-5 text-gray-500 hover:text-red-600 flex-shrink-0" title="Remove Item">
              <Trash2 className="h-4 w-4" />
            </Button>
          </div>
        ))}
        <Button variant="outline" size="sm" onClick={handleAddItem}>
          <PlusCircle className="mr-2 h-4 w-4" /> Add Dictionary Entry
        </Button>
      </div>
    );
  };

  const renderValueInput = (
    value: any,
    valueType: ValueTypeName,
    onChange: (newValue: any) => void,
    nestingLevel: number
  ) => {
    // This will become much more complex for Array, Set, Dictionary
    switch (valueType) {
      case "string":
      case "Int": // Int is string in UI, then converted
      case "Raw": // Raw is string in UI, then converted
        return (
          <Input
            type={valueType === "Int" ? "number" : "text"}
            value={value}
            onChange={(e) => onChange(e.target.value)}
            placeholder={`Enter ${valueType} value`}
            className="flex-grow"
          />
        );
      case "boolean":
        return (
          <input
            type="checkbox"
            checked={!!value}
            onChange={(e) => onChange(e.target.checked)}
            className="ml-2 h-5 w-5"
          />
        );
      // TODO: Implement Array, Set, Dictionary inputs
      case "Array":
        return renderCollectionInput(value, "Array", onChange, nestingLevel);
      case "Set":
        return renderCollectionInput(value, "Set", onChange, nestingLevel);
      case "Dictionary":
        return renderDictionaryInput(value, onChange, nestingLevel);
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

          <div className="grid grid-cols-2 gap-4 mb-4">
            {/* Private Key Input */}
            <div>
              <Label htmlFor="privateKey">Private Key</Label>
              <Input
                id="privateKey"
                type="text"
                value={privateKey}
                onChange={(e) => setPrivateKey(e.target.value)}
                onBlur={() => setPrivateKeyInteracted(true)}
                placeholder="Enter your private key"
                className={privateKeyError ? "border-red-500" : ""}
              />
              {privateKeyError && <p className="text-xs text-red-500 mt-1">{privateKeyError}</p>}
            </div>

            {/* Label Input */}
            <div>
              <Label htmlFor="podLabel">Label (Optional)</Label>
              <Input
                id="podLabel"
                type="text"
                value={label}
                onChange={(e) => setLabel(e.target.value)}
                placeholder="Enter a label for this POD"
              />
            </div>
          </div>

          <ScrollArea className="flex-grow border rounded-md p-1 pr-3 max-h-[calc(100%-4rem-2rem)]"> {/* Adjust max-height for key input */}
            {entries.length === 0 ? (
              <p className="text-sm text-gray-500 text-center py-4">
                No entries added yet. Click "Add Entry" to start.
              </p>
            ) : (
              <div className="space-y-4">
                {entries.map((entry, _index) => (
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
                                  value: e.target.value === "boolean" ? false : (e.target.value === "Array" || e.target.value === "Set" || e.target.value === "Dictionary" ? [] : ""),
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
                          {renderValueInput(entry.value, entry.valueType, (newValue) => updateEntry(entry.id, { value: newValue }), 0)}
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