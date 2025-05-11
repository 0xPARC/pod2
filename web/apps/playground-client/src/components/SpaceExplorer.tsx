import React from "react";
import { useSpaces } from "../hooks/useSpaceData";
import { useAppStore } from "../lib/store";
import { AlertTriangle, Loader2, Folder } from "lucide-react"; // Using lucide-react for icons

const SpaceExplorer: React.FC = () => {
  const { data: spaces, isLoading, error, refetch } =
    useSpaces();
  const activeSpaceId = useAppStore((state) => state.activeSpaceId);
  const setActiveSpaceId = useAppStore((state) => state.setActiveSpaceId);

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
      <h3 className="text-xs font-semibold uppercase text-gray-500 dark:text-gray-400 px-2 mb-2">
        Spaces
      </h3>
      {spaces.map((space) => (
        <button
          key={space.id}
          onClick={() => setActiveSpaceId(space.id)}
          className={`w-full flex items-center space-x-2 px-2 py-1.5 text-sm rounded-md transition-colors duration-100
                        ${activeSpaceId === space.id
              ? "bg-blue-100 dark:bg-blue-700/30 text-blue-700 dark:text-blue-300 font-medium"
              : "text-gray-700 dark:text-gray-300 hover:bg-gray-200 dark:hover:bg-gray-700"
            }`}
          title={`Space ID: ${space.id}\nCreated: ${new Date(space.created_at).toLocaleString()}`}
        >
          <Folder className="h-4 w-4 flex-shrink-0" />
          <span className="truncate">{space.id}</span>
        </button>
      ))}
    </div>
  );
};

export default SpaceExplorer; 