import { useQuery, useMutation, useQueryClient } from "@tanstack/react-query";
import {
  listSpaces,
  listPodsInSpace,
  createSpace,
  deleteSpace,
} from "../lib/backendServiceClient";
import type { SpaceInfo, PodInfo } from "../types/pod2";
import { useAppStore } from "../lib/store";

// Query key factory for spaces
const spaceKeys = {
  all: ["spaces"] as const,
  detail: (id: string) => [...spaceKeys.all, id] as const, // For future use if fetching single space details
};

// Query key factory for pods
export const podKeys = {
  all: ["pods"] as const,
  inSpace: (spaceId: string | null) =>
    [...podKeys.all, "inSpace", spaceId] as const,
  detail: (spaceId: string, podId: string) =>
    [...podKeys.inSpace(spaceId), podId] as const, // For future use
};

/**
 * Hook to fetch the list of all available spaces.
 */
export function useSpaces() {
  return useQuery<SpaceInfo[], Error>({
    queryKey: spaceKeys.all,
    queryFn: listSpaces,
    // Optional: configure staleTime, cacheTime, etc.
    // staleTime: 5 * 60 * 1000, // 5 minutes
  });
}

/**
 * Hook to fetch the list of PODs within a specific space.
 * @param spaceId The ID of the space to fetch PODs from. Query is disabled if null.
 */
export function usePodsInSpace(spaceId: string | null) {
  return useQuery<PodInfo[], Error>({
    queryKey: podKeys.inSpace(spaceId),
    queryFn: () => {
      if (!spaceId) {
        // This should ideally not be reached if `enabled` is used correctly,
        // but as a safeguard / for clarity:
        return Promise.resolve([]);
      }
      return listPodsInSpace(spaceId);
    },
    enabled: !!spaceId, // Only run the query if spaceId is truthy
    // Optional: configure staleTime, cacheTime, etc.
    // staleTime: 1 * 60 * 1000, // 1 minute, as POD list might change more often
  });
}

export function useCreateSpace() {
  const queryClient = useQueryClient();
  return useMutation({
    mutationFn: (spaceId: string) => createSpace(spaceId),
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: ["spaces"] });
    },
    // Optional: Add onError to handle errors, e.g., show a toast notification
  });
}

export function useDeleteSpace() {
  const queryClient = useQueryClient();
  const setActiveSpaceId = useAppStore((state) => state.setActiveSpaceId);
  const activeSpaceId = useAppStore((state) => state.activeSpaceId);

  return useMutation({
    mutationFn: (spaceId: string) => deleteSpace(spaceId),
    onSuccess: (_data, spaceId) => {
      if (activeSpaceId === spaceId) {
        setActiveSpaceId(null);
      }
      queryClient.invalidateQueries({ queryKey: ["spaces"] });
    },
    // Optional: Add onError to handle errors
  });
}
