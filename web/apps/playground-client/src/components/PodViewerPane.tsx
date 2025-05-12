import React from "react";
import { useAppStore } from "../lib/store";
import MainPodCard from "./MainPodCard";
import type { PodData } from "@/types/pod2"; // For type checking, added PodData and SignedPod
import SignedPodCard from "./SignedPodCard";

const PodViewerPane: React.FC = () => {
  const selectedPod = useAppStore((state) => state.selectedPodForViewing);

  if (!selectedPod) {
    return (
      <div className="p-4 h-full flex items-center justify-center bg-gray-50 dark:bg-gray-800/30">
        <p className="text-muted-foreground">
          No POD selected. Select a POD from the explorer to view its details here.
        </p>
      </div>
    );
  }

  // Explicitly type podData to help TypeScript
  const podData: PodData = selectedPod.data;

  // Determine how to display based on pod_data_variant
  let podContent;
  if (podData.pod_data_variant === "Main") {
    // The payload for Main is MainPod
    const mainPodPayload = podData.pod_data_payload;
    podContent = <MainPodCard mainPod={mainPodPayload} podId={selectedPod.id} label={selectedPod.label} />;
  } else if (podData.pod_data_variant === "Signed") {
    // The payload for Signed is SignedPod
    const signedPodPayload = podData.pod_data_payload;
    podContent = (
      <SignedPodCard
        signedPod={signedPodPayload}
        podId={selectedPod.id}
        label={selectedPod.label}
      />
    );
  } else {
    // Fallback for unknown pod_data_variant
    // This case should ideally not be reached if PodData is a discriminated union correctly handled
    podContent = (
      <p>Unknown POD data variant</p>
    );
  }

  return (
    <div className="p-4 h-full bg-gray-50 dark:bg-gray-800/30 overflow-y-auto">
      <div className="mx-auto">
        {podContent}
      </div>
    </div>
  );
};

export default PodViewerPane; 