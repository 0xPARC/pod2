import React, { useState, useEffect } from "react";
import { useAppStore } from "../lib/store";
import { useSpaces } from "../hooks/useSpaceData";
import { importPodDataToSpace, type ImportPodClientPayload } from "../lib/backendServiceClient";
import type { MainPod, SpaceInfo } from "@/types/pod2";
import { useQueryClient } from "@tanstack/react-query";
import { podKeys } from "../hooks/useSpaceData";

import { Button } from "./ui/button";
import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogFooter,
  DialogHeader,
  DialogTitle,
} from "./ui/dialog";
import { Input } from "./ui/input";
import { Label } from "./ui/label";
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from "./ui/select";
import { toast } from "sonner"; // Corrected import for sonner
import { Loader2, AlertCircle } from "lucide-react";

interface AddToSpaceDialogProps {
  isOpen: boolean;
  onOpenChange: (isOpen: boolean) => void;
  mainPodToSave: MainPod | null;
  defaultSpaceId?: string | null; // Make it optional, will use activeSpaceId if not provided
}

const AddToSpaceDialog: React.FC<AddToSpaceDialogProps> = ({
  isOpen,
  onOpenChange,
  mainPodToSave,
  defaultSpaceId,
}) => {
  const { data: spaces, isLoading: isLoadingSpaces } = useSpaces();
  const activeStoreSpaceId = useAppStore((state) => state.activeSpaceId);
  const queryClient = useQueryClient();

  const [targetSpaceId, setTargetSpaceId] = useState<string>("");
  const [podLabel, setPodLabel] = useState<string>("");
  const [isSaving, setIsSaving] = useState<boolean>(false);
  const [saveError, setSaveError] = useState<string | null>(null);

  useEffect(() => {
    if (isOpen) {
      // When dialog opens, reset state
      setPodLabel("");
      setSaveError(null);
      setIsSaving(false);
      // Set target space ID
      const initialSpaceId = defaultSpaceId || activeStoreSpaceId;
      if (initialSpaceId) {
        setTargetSpaceId(initialSpaceId);
      } else if (spaces && spaces.length > 0) {
        setTargetSpaceId(spaces[0].id); // Fallback to the first available space
      }
    }
  }, [isOpen, defaultSpaceId, activeStoreSpaceId, spaces, mainPodToSave]);

  // Effect to update targetSpaceId if spaces load after dialog is open and no valid default was set
  useEffect(() => {
    if (isOpen && !targetSpaceId && spaces && spaces.length > 0) {
      setTargetSpaceId(spaces[0].id);
    }
  }, [isOpen, targetSpaceId, spaces]);

  const handleSave = async () => {
    if (!mainPodToSave || !targetSpaceId) {
      setSaveError("Missing POD data or target space.");
      return;
    }

    setIsSaving(true);
    setSaveError(null);

    const payload: ImportPodClientPayload = {
      podType: "main",
      data: mainPodToSave,
      label: podLabel.trim() === "" ? undefined : podLabel.trim(),
    };

    try {
      const newPodInfo = await importPodDataToSpace(targetSpaceId, payload);
      toast("POD Saved Successfully", {
        description: `POD "${newPodInfo.label || newPodInfo.id}" added to space "${targetSpaceId}".`,
      });
      queryClient.invalidateQueries({ queryKey: podKeys.inSpace(targetSpaceId) });
      // Optionally, if the target space is not the active one, offer to switch or switch automatically
      // if (targetSpaceId !== activeStoreSpaceId) setActiveSpaceId(targetSpaceId);
      onOpenChange(false); // Close dialog
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : "An unknown error occurred.";
      setSaveError(errorMessage);
      toast.error("Failed to Save POD", {
        description: errorMessage,
      });
    } finally {
      setIsSaving(false);
    }
  };

  if (!mainPodToSave) return null; // Don't render if no pod data

  return (
    <Dialog open={isOpen} onOpenChange={onOpenChange}>
      <DialogContent className="sm:max-w-[425px]">
        <DialogHeader>
          <DialogTitle>Add MainPod to Space</DialogTitle>
          <DialogDescription>
            Select a space and optionally provide a label for this POD. The Pod Class will be derived automatically.
          </DialogDescription>
        </DialogHeader>
        <div className="grid gap-4 py-4">
          <div className="grid grid-cols-4 items-center gap-4">
            <Label htmlFor="targetSpace" className="text-right">
              Space
            </Label>
            {isLoadingSpaces ? (
              <div className="col-span-3 flex items-center">
                <Loader2 className="mr-2 h-4 w-4 animate-spin" /> Loading spaces...
              </div>
            ) : spaces && spaces.length > 0 ? (
              <Select
                value={targetSpaceId}
                onValueChange={setTargetSpaceId}
                disabled={isSaving}
              >
                <SelectTrigger className="col-span-3" id="targetSpace">
                  <SelectValue placeholder="Select a space" />
                </SelectTrigger>
                <SelectContent>
                  {spaces.map((space: SpaceInfo) => (
                    <SelectItem key={space.id} value={space.id}>
                      {space.id}
                    </SelectItem>
                  ))}
                </SelectContent>
              </Select>
            ) : (
              <div className="col-span-3 text-sm text-gray-500">
                No spaces available. Create one first.
              </div>
            )}
          </div>
          <div className="grid grid-cols-4 items-center gap-4">
            <Label htmlFor="podLabel" className="text-right">
              Label (Optional)
            </Label>
            <Input
              id="podLabel"
              value={podLabel}
              onChange={(e) => setPodLabel(e.target.value)}
              className="col-span-3"
              disabled={isSaving}
              placeholder="e.g., My important POD"
            />
          </div>
          {saveError && (
            <div className="col-span-4 p-2 bg-red-50 dark:bg-red-900/30 text-red-700 dark:text-red-300 rounded-md flex items-center">
              <AlertCircle className="h-5 w-5 mr-2" />
              <p className="text-sm">{saveError}</p>
            </div>
          )}
        </div>
        <DialogFooter>
          <Button variant="outline" onClick={() => onOpenChange(false)} disabled={isSaving}>
            Cancel
          </Button>
          <Button onClick={handleSave} disabled={isSaving || isLoadingSpaces || !targetSpaceId || !spaces || spaces.length === 0}>
            {isSaving ? <Loader2 className="mr-2 h-4 w-4 animate-spin" /> : null}
            Add POD
          </Button>
        </DialogFooter>
      </DialogContent>
    </Dialog>
  );
};

export default AddToSpaceDialog; 