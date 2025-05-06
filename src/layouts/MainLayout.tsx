import React from 'react';
import { Panel, PanelGroup, PanelResizeHandle } from 'react-resizable-panels';
import Sidebar from '../components/Sidebar';
import CodeEditor from '../components/CodeEditor';
import AnalysisPanel from '../components/AnalysisPanel';
import { useLayoutContext } from '../context/LayoutContext';

const MainLayout: React.FC = () => {
  const { activeMode } = useLayoutContext();

  return (
    <div className="flex flex-1 overflow-hidden">
      <Sidebar />
      <div className="flex-1">
        <PanelGroup direction="vertical" className="h-full">
          <Panel defaultSize={50} minSize={20}>
            <div className="h-full p-4">
              <h2 className="text-xl font-semibold mb-3 text-blue-400">
                {activeMode === 'verification' ? 'Program Verification' : 'Program Equivalence'}
              </h2>
              {activeMode === 'verification' ? (
                <CodeEditor id="single-program" label="Program" placeholder="Enter your program here..." />
              ) : (
                <div className="grid grid-cols-2 gap-4 h-full">
                  <CodeEditor id="program-1" label="Program 1" placeholder="Enter first program..." />
                  <CodeEditor id="program-2" label="Program 2" placeholder="Enter second program..." />
                </div>
              )}
            </div>
          </Panel>
          <PanelResizeHandle className="h-2 bg-gray-800 hover:bg-blue-700 transition-colors cursor-row-resize flex items-center justify-center">
            <div className="w-8 h-1 bg-gray-600 rounded-full"></div>
          </PanelResizeHandle>
          <Panel defaultSize={50} minSize={20}>
            <AnalysisPanel />
          </Panel>
        </PanelGroup>
      </div>
    </div>
  );
};

export default MainLayout;