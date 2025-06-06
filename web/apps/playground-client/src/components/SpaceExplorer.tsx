import React, { useState } from "react";
import { useSpaces, useCreateSpace, useDeleteSpace } from "../hooks/useSpaceData";
import { useAppStore } from "../lib/store";
import { AlertTriangle, Loader2, Folder, Plus, MoreHorizontal, Trash2 } from "lucide-react"; // Using lucide-react for icons
import { Button } from "./ui/button";
import {
  DropdownMenu,
  DropdownMenuContent,
  DropdownMenuItem,
  DropdownMenuTrigger,
} from "./ui/dropdown-menu";
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
  DialogDescription,
  DialogFooter,
} from "./ui/dialog";
import { Input } from "./ui/input";
import { toast } from "sonner";

const SpaceExplorer: React.FC = () => {
  const { data: spaces, isLoading, error, refetch } =
    useSpaces();
  const activeSpaceId = useAppStore((state) => state.activeSpaceId);
  const setActiveSpaceId = useAppStore((state) => state.setActiveSpaceId);

  const createSpaceMutation = useCreateSpace();
  const deleteSpaceMutation = useDeleteSpace();

  const [isCreateDialogOpen, setIsCreateDialogOpen] = useState(false);
  const [newSpaceName, setNewSpaceName] = useState("");
  const [deletingSpaceId, setDeletingSpaceId] = useState<string | null>(null);

  const handleCreateSpace = async () => {
    if (!newSpaceName.trim()) {
      toast.error("Space name cannot be empty.");
      return;
    }
    try {
      await createSpaceMutation.mutateAsync(newSpaceName.trim());
      toast.success(`Space "${newSpaceName.trim()}" created.`);
      setNewSpaceName("");
      setIsCreateDialogOpen(false);
    } catch (err: any) {
      toast.error("Failed to create space", {
        description: err.message || "An unknown error occurred.",
      });
    }
  };

  const handleDeleteSpace = async () => {
    if (!deletingSpaceId) return;
    try {
      await deleteSpaceMutation.mutateAsync(deletingSpaceId);
      toast.success(`Space "${deletingSpaceId}" deleted.`);
      setDeletingSpaceId(null);
    } catch (err: any) {
      toast.error("Failed to delete space", {
        description: err.message || "An unknown error occurred.",
      });
    }
  };

  if (isLoading) {
    return (
      <div className="p-4 text-sm text-gray-500 dark:text-gray-400 flex items-center">
        <Loader2 className="mr-2 h-4 w-4 animate-spin" />
        Loading spaces...
      </div>
    );
  }

  if (error) {
    return (
      <div className="p-4 text-sm text-red-600 dark:text-red-400">
        <div className="flex items-center mb-2">
          <AlertTriangle className="mr-2 h-5 w-5" />
          Error loading spaces: {error.message}
        </div>
        <button
          onClick={() => refetch()} // TanStack Query's refetch function
          className="px-3 py-1 text-xs bg-blue-500 hover:bg-blue-600 text-white rounded"
        >
          Retry
        </button>
      </div>
    );
  }

  if (!spaces || spaces.length === 0) {
    return (
      <div className="p-4 text-sm text-gray-500 dark:text-gray-400">
        No spaces found.
      </div>
    );
  }

  return (
    <div className="p-2 space-y-1">
      <div className="flex items-center justify-between px-2 mb-2">
        <h3 className="text-xs font-semibold uppercase text-gray-500 dark:text-gray-400">
          Spaces
        </h3>
        <Button
          variant="ghost"
          size="icon"
          className="h-6 w-6"
          onClick={() => setIsCreateDialogOpen(true)}
          title="Create new space"
        >
          <Plus className="h-4 w-4" />
        </Button>
      </div>
      {spaces.map((space) => (
        <div
          key={space.id}
          className={`group w-full flex items-center justify-between space-x-2 px-2 py-1.5 text-sm rounded-md transition-colors duration-100
                        ${activeSpaceId === space.id
              ? "bg-blue-100 dark:bg-blue-700/30 text-blue-700 dark:text-blue-300 font-medium"
              : "text-gray-700 dark:text-gray-300 hover:bg-gray-200 dark:hover:bg-gray-700"
            }`}
        >
          <button
            onClick={() => setActiveSpaceId(space.id)}
            className="flex-grow flex items-center space-x-2 text-left"
            title={`Space ID: ${space.id}\nCreated: ${new Date(space.created_at).toLocaleString()}`}
          >
            <Folder className="h-4 w-4 flex-shrink-0" />
            <span className="truncate">{space.id}</span>
          </button>
          <DropdownMenu>
            <DropdownMenuTrigger asChild>
              <Button variant="ghost" size="icon" className="h-6 w-6 opacity-0 group-hover:opacity-100">
                <MoreHorizontal className="h-4 w-4" />
              </Button>
            </DropdownMenuTrigger>
            <DropdownMenuContent>
              <DropdownMenuItem
                className="text-red-600"
                onSelect={() => setDeletingSpaceId(space.id)}
              >
                <Trash2 className="mr-2 h-4 w-4" />
                Delete
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>
        </div>
      ))}
      {/* Create Space Dialog */}
      <Dialog open={isCreateDialogOpen} onOpenChange={setIsCreateDialogOpen}>
        <DialogContent>
          <DialogHeader>
            <DialogTitle>Create New Space</DialogTitle>
          </DialogHeader>
          <div className="py-4">
            <Input
              placeholder="Enter space name..."
              value={newSpaceName}
              onChange={(e) => setNewSpaceName(e.target.value)}
              onKeyDown={(e) => e.key === 'Enter' && handleCreateSpace()}
            />
          </div>
          <DialogFooter>
            <Button variant="outline" onClick={() => setIsCreateDialogOpen(false)}>Cancel</Button>
            <Button onClick={handleCreateSpace} disabled={createSpaceMutation.isPending}>
              {createSpaceMutation.isPending ? <Loader2 className="mr-2 h-4 w-4 animate-spin" /> : null}
              Create
            </Button>
          </DialogFooter>
        </DialogContent>
      </Dialog>

      {/* Delete Confirmation Dialog */}
      <Dialog open={!!deletingSpaceId} onOpenChange={() => setDeletingSpaceId(null)}>
        <DialogContent>
          <DialogHeader>
            <DialogTitle>Are you sure?</DialogTitle>
            <DialogDescription>
              This will permanently delete the space "{deletingSpaceId}" and all pods within it. This action cannot be undone.
            </DialogDescription>
          </DialogHeader>
          <DialogFooter>
            <Button variant="outline" onClick={() => setDeletingSpaceId(null)}>Cancel</Button>
            <Button variant="destructive" onClick={handleDeleteSpace} disabled={deleteSpaceMutation.isPending}>
              {deleteSpaceMutation.isPending ? <Loader2 className="mr-2 h-4 w-4 animate-spin" /> : null}
              Delete
            </Button>
          </DialogFooter>
        </DialogContent>
      </Dialog>
    </div>
  );
};

export default SpaceExplorer; 