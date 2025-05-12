import React from "react";
import EditorPane from "./components/EditorPane"; // Import the EditorPane component
import ControlsPane from "./components/ControlsPane"; // Import ControlsPane
import ResultsPane from "./components/ResultsPane"; // Import ResultsPane
import IdeLayout from "./components/IdeLayout"; // Import the new layout
import SpaceExplorer from "./components/SpaceExplorer"; // Import SpaceExplorer
import PodList from "./components/PodList"; // Import PodList
import { Toaster } from "@/components/ui/sonner"; // Added Toaster import

interface AppProps {
  children?: React.ReactNode; // For router outlet
}

function App({ children }: AppProps) {
  // Placeholder content for the explorer - to be developed later
  const explorerPaneContent = (
    <div className="h-full flex flex-col">
      <SpaceExplorer />
      <PodList />
    </div>
  );

  return (
    <>
      <IdeLayout
        //   controlsContent={<ControlsPane />}
        explorerContent={explorerPaneContent}
        editorContent={<EditorPane />}
        resultsContent={<ResultsPane />}
      />
      {/* Render children from router (e.g., Outlet for pages, Devtools) as siblings */}
      {children}
      {/* Toaster for notifications, should be at a high level */}
      <Toaster richColors closeButton position="top-right" />
    </>
  );
}

export default App;
