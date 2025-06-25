import React, { useRef, useEffect } from "react";
import { useAppStore } from "../lib/store";
import {
  ResizablePanelGroup,
  ResizablePanel,
  ResizableHandle,
} from "./ui/resizable"; // Keep shadcn components
import type { ImperativePanelGroupHandle } from "react-resizable-panels"; // Import type from base library
import { PanelLeftClose, PanelLeftOpen, PanelBottomClose, PanelBottomOpen } from "lucide-react"; // Example icons
import MainAreaTabs from "./MainAreaTabs"; // Import MainAreaTabs
import PodViewerPane from "./PodViewerPane"; // Import PodViewerPane
import { LeftSidebar } from "./LeftSidebar";
const COLLAPSED_RESULTS_PANE_SIZE = 4; // Percentage

const IdeLayout: React.FC<{
  explorerContent: React.ReactNode;
  editorContent: React.ReactNode;
  resultsContent: React.ReactNode;
  // controlsContent: React.ReactNode;
}> = ({
  explorerContent,
  editorContent,
  resultsContent,
  //  controlsContent,
}) => {
    const isExplorerCollapsed = useAppStore(
      (state) => state.isExplorerCollapsed
    );
    const toggleExplorer = useAppStore((state) => state.toggleExplorer);

    const isResultsPaneOpen = useAppStore((state) => state.isResultsPaneOpen);
    const setIsResultsPaneOpen = useAppStore(
      (state) => state.setIsResultsPaneOpen
    );
    const resultsPaneSize = useAppStore((state) => state.resultsPaneSize);
    const setResultsPaneSize = useAppStore((state) => state.setResultsPaneSize);
    const isStoreInitialized = useAppStore((state) => state.isStoreInitialized); // Get isStoreInitialized
    const activeMainAreaTab = useAppStore((state) => state.activeMainAreaTab); // Get active tab

    const verticalPanelGroupRef = useRef<ImperativePanelGroupHandle>(null);

    // Handler for when the main horizontal panel group is resized
    const handleHorizontalResize = (sizes: number[]) => {
      // For a 2-panel group, sizes[0] is the explorer, sizes[1] is the main content
      // We don't strictly need to store the explorer width for now if
      // collapsing is handled by a dedicated state.
      // If we wanted to store a specific "restored" width, we could do:
      // if (!isExplorerCollapsed && sizes.length > 0) {
      //   storeExplorerWidth(sizes[0]);
      // }
    };

    // Handler for when the vertical panel group (editor/results) is resized
    const handleVerticalResize = (sizes: number[]) => {
      // For a 2-panel group, sizes[0] is editor, sizes[1] is results
      if (sizes.length > 1) {
        // Assuming the results pane is the second panel
        // setResultsPaneSize(sizes[1]); // This would store the actual pixel/relative value
        // For simplicity now, let's assume the component manages its internal relative sizing.
        // We only need to control the open/closed state and initial/default size.
      }
    };

    const handleResultsToggle = () => {
      setIsResultsPaneOpen(!isResultsPaneOpen);
    };

    useEffect(() => {
      if (verticalPanelGroupRef.current) {
        if (isResultsPaneOpen) {
          verticalPanelGroupRef.current.setLayout([
            100 - resultsPaneSize, // Editor pane size
            resultsPaneSize,       // Results pane size (expanded)
          ]);
        } else {
          verticalPanelGroupRef.current.setLayout([
            100 - COLLAPSED_RESULTS_PANE_SIZE, // Editor pane size
            COLLAPSED_RESULTS_PANE_SIZE,       // Results pane size (collapsed)
          ]);
        }
      }
    }, [isResultsPaneOpen, resultsPaneSize]); // Re-run when isResultsPaneOpen or resultsPaneSize changes

    return (
      <div className="flex flex-col h-screen">
        {/* Controls Pane (e.g., Execute button) could go here or above App.tsx layout */}
        <ResizablePanelGroup
          direction="horizontal"
          className="flex-grow border dark:border-gray-700"
          onLayout={(sizes: number[]) => handleHorizontalResize(sizes)}
        >
          <LeftSidebar toggleExplorer={toggleExplorer} isExplorerCollapsed={isExplorerCollapsed} explorerContent={explorerContent} />
          {!isExplorerCollapsed && <ResizableHandle withHandle className="bg-gray-100 dark:bg-gray-800" />}

          {/* Right Main Content Panel */}
          <ResizablePanel defaultSize={isExplorerCollapsed ? 100 : 80}>
            <ResizablePanelGroup
              ref={verticalPanelGroupRef} // Assign the ref
              direction="vertical"
              onLayout={(sizes: number[]) => {
                // Store the size of the results pane when it's dragged by the user
                // Only update if the pane is considered open and the new size is significant
                if (isResultsPaneOpen && sizes.length > 1 && sizes[1] > COLLAPSED_RESULTS_PANE_SIZE + 1) {
                  setResultsPaneSize(sizes[1]);
                }
              }}
            >
              {/* Editor Pane (Top) */}
              <ResizablePanel
                // defaultSize is less critical now as useEffect controls layout
                // Set a sensible initial default, e.g., 70 or calculate based on initial resultsPaneSize
                defaultSize={isStoreInitialized ? (100 - (isResultsPaneOpen ? resultsPaneSize : COLLAPSED_RESULTS_PANE_SIZE)) : 70}
                minSize={30}
                order={1}
              >
                <div className="h-full bg-gray-200 dark:bg-gray-800 py-1">
                  {/* Render MainAreaTabs and then conditionally EditorPane or PodViewerPane */}
                  <MainAreaTabs />
                  <div className="flex-grow overflow-auto h-[calc(100%-2.5rem)]"> {/* Adjust height based on tab bar height */}
                    {activeMainAreaTab === "editor" && editorContent}
                    {activeMainAreaTab === "podViewer" && <PodViewerPane />}
                  </div>
                </div>
              </ResizablePanel>

              {/* Results Pane Handle - always show */}
              <ResizableHandle withHandle className="bg-gray-100 dark:bg-gray-800 data-[resize-handle-state=drag]:bg-blue-500 data-[resize-handle-state=hover]:bg-blue-300" />

              {/* Results Pane Content (Bottom) */}
              <ResizablePanel
                // defaultSize is less critical now
                defaultSize={isStoreInitialized ? (isResultsPaneOpen ? resultsPaneSize : COLLAPSED_RESULTS_PANE_SIZE) : 30}
                minSize={COLLAPSED_RESULTS_PANE_SIZE} // Min size for collapsed state bar (matches collapsedSize)
                maxSize={75}
                collapsible={true}
                collapsedSize={COLLAPSED_RESULTS_PANE_SIZE} // Represents the size when only the toggle bar is shown
                onCollapse={() => {
                  if (isResultsPaneOpen) setIsResultsPaneOpen(false); // If dragged to collapse
                }}
                onExpand={() => {
                  if (!isResultsPaneOpen) setIsResultsPaneOpen(true); // If dragged to expand
                }}
                order={2}
              >
                <div className="h-full p-1 flex flex-col bg-gray-200 dark:bg-gray-800">
                  <div className="flex items-center space-x-2 mb-1">
                    <button
                      onClick={handleResultsToggle} // This is the IdeLayout's toggle function
                      className="p-1 hover:bg-gray-200 dark:hover:bg-gray-700 rounded text-gray-600 dark:text-gray-400"
                      title={isResultsPaneOpen ? "Collapse Results" : "Open Results"}
                    >
                      {isResultsPaneOpen ? <PanelBottomClose size={18} /> : <PanelBottomOpen size={18} />}
                    </button>
                    <div className="text-xs font-medium uppercase text-gray-800 dark:text-gray-200">
                      Results
                    </div>
                  </div>
                  {isResultsPaneOpen && (
                    <div className="flex-grow overflow-auto">{resultsContent}</div>
                  )}
                  {!isResultsPaneOpen && (
                    <div className="flex-grow flex items-center justify-center text-xs text-gray-500 dark:text-gray-400">
                      {/* Optionally, show a placeholder message when collapsed and empty */}
                      {/* Click button above to open results */}
                    </div>
                  )}
                </div>
              </ResizablePanel>
            </ResizablePanelGroup>
          </ResizablePanel>
        </ResizablePanelGroup>
      </div>
    );
  };

export default IdeLayout; 