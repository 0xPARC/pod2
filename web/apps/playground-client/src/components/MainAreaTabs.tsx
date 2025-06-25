import React from "react";
import { useAppStore, type MainAreaTab } from "../lib/store";
import { Button } from "./ui/button"; // Using shadcn Button
import { Code, Package } from "lucide-react"; // Icons for tabs

const MainAreaTabs: React.FC = () => {
  const activeTab = useAppStore((state) => state.activeMainAreaTab);
  const setActiveTab = useAppStore((state) => state.setActiveMainAreaTab);

  const handleTabClick = (tab: MainAreaTab) => {
    setActiveTab(tab);
  };

  return (
    <div className="flex border-b border-gray-300 dark:border-gray-700 bg-gray-100 dark:bg-gray-900 select-none">
      <Button
        variant={activeTab === "editor" ? "secondary" : "ghost"}
        size="sm"
        onClick={() => handleTabClick("editor")}
        className={`rounded-none px-4 py-2 h-10 border-r border-gray-300 dark:border-gray-700 flex items-center space-x-2 ${activeTab === "editor" ? "text-gray-800 dark:text-gray-200 font-semibold" : "text-muted-foreground"}`}
      >
        <Code className="h-4 w-4" />
        <span>Code Editor</span>
      </Button>
      <Button
        variant={activeTab === "podViewer" ? "secondary" : "ghost"}
        size="sm"
        onClick={() => handleTabClick("podViewer")}
        className={`rounded-none px-4 py-2 h-10 flex items-center space-x-2 ${activeTab === "podViewer" ? "text-gray-800 dark:text-gray-200 font-semibold" : "text-muted-foreground"}`}
      >
        <Package className="h-4 w-4" />
        <span>POD Viewer</span>
      </Button>
      {/* Empty div to fill remaining space and push tabs to the left, if needed, or for future tab controls */}
      <div className="flex-grow border-b border-gray-300 dark:border-gray-700"></div>
    </div>
  );
};

export default MainAreaTabs; 