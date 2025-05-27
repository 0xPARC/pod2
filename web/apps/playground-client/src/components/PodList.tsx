import React, { useState } from "react";
import { useQueryClient, useMutation } from "@tanstack/react-query";
import { deletePodFromSpace } from "../lib/backendServiceClient";
import { useAppStore } from "../lib/store";
import { usePodsInSpace, podKeys } from "../hooks/useSpaceData";
import { AlertTriangle, Loader2, FileText, FileCheck2, FilePenLine, Trash2, PlusCircle, FilePen, Import, ClipboardPaste } from "lucide-react";
import type { PodInfo } from "@/types/pod2";
import { ScrollArea } from "@/components/ui/scroll-area";
import { Button } from "@/components/ui/button";
import ImportPodDialog from "./ImportPodDialog";
import CreateSignedPodDialog from "./CreateSignedPodDialog";
import {
  AlertDialog,
  AlertDialogAction,
  AlertDialogCancel,
  AlertDialogContent,
  AlertDialogDescription,
  AlertDialogFooter,
  AlertDialogHeader,
  AlertDialogTitle,
  AlertDialogTrigger,
} from "@/components/ui/alert-dialog";
import { toast } from "sonner";
import { DropdownMenu, DropdownMenuContent, DropdownMenuItem, DropdownMenuTrigger } from "./ui/dropdown-menu";


function truncateText(text: string, maxLength: number = 16) {
  if (text.length <= maxLength) return text;
  return text.slice(0, maxLength) + "...";
}

const getErrorMessage = (err: unknown): string => {
  if (err instanceof Error) {
    return err.message;
  }
  return String(err);
};

interface PodListItemProps {
  pod: PodInfo;
  activeSpaceId: string | null; // Needed for the delete dialog message
  deleteMutation: ReturnType<typeof useMutation<void, Error, { spaceId: string; podId: string }>>;
  onDeletePod: (podId: string) => void;
  onSelectPod: (pod: PodInfo) => void; // Added prop for selecting a POD
}

const PodListItem: React.FC<PodListItemProps> = ({ pod, activeSpaceId, deleteMutation, onDeletePod, onSelectPod }) => {
  let icon = <FileText className="mr-2 h-4 w-4 flex-shrink-0 text-gray-500 dark:text-gray-400" />;
  let displayType = pod.pod_type; // e.g., "main" or "signed"

  if (pod.data.pod_data_variant === "Main") {
    icon = <FileCheck2 className="mr-2 h-4 w-4 flex-shrink-0 text-sky-500 dark:text-sky-400" />;
    displayType = `${pod.data.pod_data_payload.podType || 'N/A'}`;
  } else if (pod.data.pod_data_variant === "Signed") {
    icon = <FilePenLine className="mr-2 h-4 w-4 flex-shrink-0 text-teal-500 dark:text-teal-400" />;
    displayType = `${pod.data.pod_data_payload.podType || 'N/A'}`;
  }

  return (
    <li
      key={pod.id}
      className="flex items-center justify-between px-2 py-1.5 text-sm text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700 rounded-md group cursor-pointer"
      title={`ID: ${pod.id}\nLabel: ${pod.label || 'None'}\nCreated: ${new Date(pod.created_at).toLocaleString()}`}
      onClick={() => onSelectPod(pod)} // Call onSelectPod when the item is clicked
    >
      <div className="flex items-center truncate flex-grow">
        {icon}
        <span className="truncate font-medium max-w-[16ch]">{pod.label || pod.id}</span>
        <span className="ml-1.5 text-xs text-gray-500 dark:text-gray-400 whitespace-nowrap flex-shrink-0">
          ({displayType})
        </span>
      </div>
      <AlertDialog>
        <AlertDialogTrigger asChild>
          <Button
            variant="ghost"
            size="icon"
            className="h-6 w-6 opacity-0 group-hover:opacity-100 focus:opacity-100 transition-opacity flex-shrink-0 ml-1 pointer-events-auto"
            title={`Delete POD ${pod.label || pod.id}`}
            disabled={deleteMutation.isPending && deleteMutation.variables?.podId === pod.id}
          >
            {deleteMutation.isPending && deleteMutation.variables?.podId === pod.id ? (
              <Loader2 className="h-3.5 w-3.5 animate-spin" />
            ) : (
              <Trash2 className="h-3.5 w-3.5 text-red-500 dark:text-red-400" />
            )}
          </Button>
        </AlertDialogTrigger>
        <AlertDialogContent>
          <AlertDialogHeader>
            <AlertDialogTitle>Are you sure?</AlertDialogTitle>
            <AlertDialogDescription>
              This action cannot be undone. This will permanently delete the
              POD "<strong>{truncateText(pod.label || pod.id)}</strong>" (ID: {truncateText(pod.id)}) from space "<strong>{activeSpaceId}</strong>".
            </AlertDialogDescription>
          </AlertDialogHeader>
          <AlertDialogFooter>
            <AlertDialogCancel>Cancel</AlertDialogCancel>
            <AlertDialogAction
              onClick={() => onDeletePod(pod.id)}
              className="bg-red-600 hover:bg-red-700 dark:bg-red-500 dark:hover:bg-red-600 text-white dark:text-white"
            >
              Delete
            </AlertDialogAction>
          </AlertDialogFooter>
        </AlertDialogContent>
      </AlertDialog>
    </li>
  );
};

function PodList() {
  const activeSpaceId = useAppStore((state) => state.activeSpaceId);
  const [isImportDialogOpen, setIsImportDialogOpen] = useState(false); // State for dialog
  const [isCreateSignedPodDialogOpen, setIsCreateSignedPodDialogOpen] = useState(false); // State for new dialog
  const setActiveMainAreaTab = useAppStore((state) => state.setActiveMainAreaTab); // Get action
  const setSelectedPodForViewing = useAppStore((state) => state.setSelectedPodForViewing); // Get action
  const {
    data: pods = [],
    isLoading,
    isError,
    error,
    refetch,
  } = usePodsInSpace(activeSpaceId);
  const queryClient = useQueryClient();

  const deleteMutation = useMutation<void, Error, { spaceId: string; podId: string }>({
    mutationFn: ({ spaceId, podId }: { spaceId: string; podId: string }) =>
      deletePodFromSpace(spaceId, podId),
    onSuccess: (_, variables) => {
      toast(
        `POD "${variables.podId}" deleted successfully from space "${variables.spaceId}".`
      );
      queryClient.invalidateQueries({
        queryKey: podKeys.inSpace(variables.spaceId),
      });
    },
    onError: (err, variables) => {
      toast.error(
        `Failed to delete POD "${variables.podId}": ${getErrorMessage(err)}`
      );
    },
  });

  const handleDeletePod = (podId: string) => {
    if (!activeSpaceId) {
      toast.error("No active space selected for deletion.");
      return;
    }
    deleteMutation.mutate({ spaceId: activeSpaceId, podId });
  };

  const handleSelectPod = (pod: PodInfo) => {
    setSelectedPodForViewing(pod);
    setActiveMainAreaTab("podViewer");
  };

  if (!activeSpaceId) {
    return (
      <div className="p-4 border-t border-gray-200 dark:border-gray-700 flex-grow min-h-0 flex items-center justify-center">
        <p className="text-sm text-gray-500 dark:text-gray-400">
          Select a space to view its PODs.
        </p>
      </div>
    );
  }

  if (isLoading) {
    return (
      <div className="p-4 text-sm text-gray-500 dark:text-gray-400 flex items-center justify-center border-t border-gray-200 dark:border-gray-700 mt-2 pt-2 min-h-[100px]">
        <Loader2 className="mr-2 h-4 w-4 animate-spin" />
        Loading PODs for {activeSpaceId}...
      </div>
    );
  }

  if (isError) {
    return (
      <div className="p-4 text-sm border-t border-gray-200 dark:border-gray-700 mt-2 pt-2 min-h-[100px]">
        <div className="flex items-center mb-2 text-red-600 dark:text-red-400">
          <AlertTriangle className="mr-2 h-5 w-5 flex-shrink-0" />
          Error loading PODs: {getErrorMessage(error)}
        </div>
        <Button
          onClick={() => refetch()}
          variant="outline"
          size="sm"
        >
          Retry
        </Button>
      </div>
    );
  }

  return (
    <div className="p-2 border-t border-gray-200 dark:border-gray-700 flex-grow min-h-0">
      <div className="flex justify-between items-center mb-2 px-1">
        <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-300">
          {activeSpaceId ? `PODs in ${activeSpaceId}` : "Select a Space"}
        </h3>
        {activeSpaceId && (
          <DropdownMenu>
            <DropdownMenuTrigger asChild>
              <Button variant="outline" title="Add POD">
                <PlusCircle className="h-4 w-4" /> Add
              </Button>
            </DropdownMenuTrigger>
            <DropdownMenuContent align="end">
              <DropdownMenuItem onClick={() => setIsCreateSignedPodDialogOpen(true)}>
                <FilePenLine className="h-4 w-4" /> Sign POD
              </DropdownMenuItem>
              <DropdownMenuItem onClick={() => setIsImportDialogOpen(true)}>
                <ClipboardPaste className="h-4 w-4" /> Import POD
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>
        )}
      </div>
      <ScrollArea className="h-[calc(100%-3rem)]">
        {pods.length === 0 && (
          <p className="text-xs text-gray-500 dark:text-gray-400 px-1 py-4 text-center">
            No PODs in this space.
          </p>
        )}
        <ul className="space-y-1">
          {pods.map((pod) => (
            <PodListItem
              key={pod.id}
              pod={pod}
              activeSpaceId={activeSpaceId}
              deleteMutation={deleteMutation}
              onDeletePod={handleDeletePod}
              onSelectPod={handleSelectPod} // Pass the handler to PodListItem
            />
          ))}
        </ul>
      </ScrollArea>
      <ImportPodDialog
        isOpen={isImportDialogOpen}
        onOpenChange={setIsImportDialogOpen}
        activeSpaceId={activeSpaceId}
      />
      <CreateSignedPodDialog
        isOpen={isCreateSignedPodDialogOpen}
        onOpenChange={setIsCreateSignedPodDialogOpen}
        activeSpaceId={activeSpaceId}
      />
    </div>
  );
}

export default PodList; 