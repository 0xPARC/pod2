import React from "react";
import type { MainPod } from "@/types/pod2"; // Adjusted path

interface MainPodCardProps {
  mainPod: MainPod;
  // onClick?: () => void; // For future "open in tab" functionality
}

const MainPodCard: React.FC<MainPodCardProps> = ({ mainPod }) => {
  const statementCount = mainPod.publicStatements?.length || 0;

  // Placeholder icon, can be replaced with an SVG or icon library component
  const PodIcon = () => <span style={{ marginRight: "8px" }}>🗃️</span>;

  return (
    <div className="bg-gray-50 dark:bg-gray-700 border border-gray-300 dark:border-gray-600 p-3 rounded-md shadow-sm">
      <div className="font-semibold text-md mb-1 flex items-center text-gray-800 dark:text-gray-200">
        <PodIcon /> MainPod
      </div>
      <div className="text-sm text-gray-700 dark:text-gray-300 space-y-0.5">
        <p>
          <span className="font-medium">Type:</span> {mainPod.podType}
        </p>
        <p>
          <span className="font-medium">Public Statements:</span>{" "}
          {statementCount}
        </p>
      </div>
      {/* Future: Add a "View Details" button or make the card clickable */}
      {/* <button className="mt-2 text-xs text-blue-500 hover:text-blue-700">View Details</button> */}
    </div>
  );
};

export default MainPodCard;
