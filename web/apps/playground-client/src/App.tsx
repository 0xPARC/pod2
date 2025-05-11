import React from 'react';
import EditorPane from './components/EditorPane'; // Import the EditorPane component
import ControlsPane from './components/ControlsPane'; // Import ControlsPane
import ResultsPane from './components/ResultsPane'; // Import ResultsPane

interface AppProps {
  children?: React.ReactNode; // Define children prop
}

function App({ children }: AppProps) { // Destructure children
  return (
    <div className="flex flex-col h-screen bg-gray-100 dark:bg-gray-900 text-gray-900 dark:text-gray-100">
      {/* Controls Pane */}
      <ControlsPane />

      <div className="flex flex-row flex-grow overflow-hidden">
        {/* Editor Pane */}
        <div className="flex-grow p-4 border-r border-gray-300 dark:border-gray-700 flex flex-col">
          <h2 className="text-lg font-semibold mb-2">Editor Pane</h2>
          <div className="w-full flex-grow bg-white dark:bg-gray-800 border border-gray-300 dark:border-gray-600 rounded overflow-hidden">
            {/* Monaco Editor will be integrated here */}
            <EditorPane />
          </div>
        </div>

        {/* Results Pane */}
        <div className="w-1/3 p-4 flex-shrink-0 flex flex-col">
          <h2 className="text-lg font-semibold mb-2">Results Pane</h2>
          {/* ResultsPane component will fill the remaining space */}
          <div className="w-full flex-grow overflow-hidden">
            <ResultsPane />
          </div>
        </div>
      </div>
      {/* Render children, which will include Outlet and Devtools */}
      {children}
    </div>
  );
}

export default App; 