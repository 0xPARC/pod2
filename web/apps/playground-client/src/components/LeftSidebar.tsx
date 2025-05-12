import { Github, PanelLeftClose, PanelLeftOpen } from "lucide-react";
import { ResizablePanel } from "./ui/resizable";
import { ModeToggle } from "./mode-toggle";
import { Button } from "./ui/button";

export function LeftSidebar({ toggleExplorer, isExplorerCollapsed, explorerContent }: { toggleExplorer: () => void, isExplorerCollapsed: boolean, explorerContent: React.ReactNode }) {
  return (
    <>
      {/* Left Explorer Panel */}
      {!isExplorerCollapsed && (
        <ResizablePanel
          defaultSize={20} // Default to 20% width
          minSize={15}
          collapsible={true}

          collapsedSize={0} // Effectively hides it when collapsed via prop
          onCollapse={toggleExplorer} // Or setExplorerCollapsed(true)
          // onExpand={() => setExplorerCollapsed(false)} // If using internal collapse
          className="min-w-[200px]" // Example min width in pixels
        >
          <div className="h-full p-2 flex flex-col bg-gray-200 dark:bg-gray-800 justify-between">
            <div>
              <div className="font-bold uppercase text-lg tracking-wider text-gray-800/90 dark:text-gray-200 px-2 mb-4">POD Playground</div>
              <div className="flex items-center justify-between mb-2">

                <div className="text-gray-800 dark:text-gray-200 font-medium uppercase text-xs tracking-wide pl-1">Browse</div>
                <button
                  onClick={toggleExplorer}
                  className="p-1 mb-0 self-start hover:bg-gray-200 dark:hover:bg-gray-700 rounded text-gray-600 dark:text-gray-400"
                  title={isExplorerCollapsed ? "Open Explorer" : "Collapse Explorer"}
                >
                  <PanelLeftClose size={20} />
                </button>
              </div>
              {explorerContent}
            </div>
            <div className="px-2 pt-2 flex items-center space-x-3">
              <a href="https://github.com/0xPARC/pod2/" target="_blank" rel="noopener noreferrer" title="POD2 source code">
                <Button variant="outline" size="icon">
                  <Github className="h-4 w-4" />
                </Button>
              </a>
              <ModeToggle />
            </div>
          </div>

        </ResizablePanel>
      )}
      {isExplorerCollapsed && (
        <div className="relative h-full flex flex-col items-center p-2 bg-gray-100 dark:bg-gray-800 border-r dark:border-gray-700 space-y-2">
          <button
            onClick={toggleExplorer}
            className="p-1 hover:bg-gray-200 dark:hover:bg-gray-700 rounded text-gray-600 dark:text-gray-400"
            title={isExplorerCollapsed ? "Open Explorer" : "Collapse Explorer"}
          >
            <PanelLeftOpen size={20} />
          </button>
          <div className="text-gray-800 dark:text-gray-200 font-medium uppercase text-xs tracking-wide rotate-270 absolute top-[68px]">Browse</div>
        </div>
      )}



    </>
  )
}