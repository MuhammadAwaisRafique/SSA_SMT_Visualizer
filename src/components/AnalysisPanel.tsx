import React, { useState } from 'react';
import { Play, CheckCircle, Loader } from 'lucide-react';
import { useLayoutContext } from '../context/LayoutContext';
import { useAnalysisStore } from '../store/analysisStore';
import SyntaxHighlighter from 'react-syntax-highlighter';
import { vs2015 } from 'react-syntax-highlighter/dist/esm/styles/hljs';
import { motion, AnimatePresence } from 'framer-motion';

const tabs = ['SSA Form', 'SMT Constraints', 'Results', 'Visualization'];

const AnalysisPanel: React.FC = () => {
  const [activeTab, setActiveTab] = useState(0);
  const [unrollDepth, setUnrollDepth] = useState(3);
  const [loading, setLoading] = useState(false);
  const { activeMode } = useLayoutContext();
  const { codeMap } = useAnalysisStore();

  const handleAnalysis = () => {
    setLoading(true);
    // Mock analysis - would call backend API in real implementation
    setTimeout(() => {
      setLoading(false);
    }, 1500);
  };

  const ssaExample = `// SSA Form
x_0 := 3;
if (x_0 < 5) {
  y_0 := x_0 + 1;
} else {
  y_1 := x_0 - 1;
}
y_2 := PHI(y_0, y_1);
assert(y_2 > 0);`;

  const smtExample = `(declare-const x_0 Int)
(declare-const y_0 Int)
(declare-const y_1 Int)
(declare-const y_2 Int)
(declare-const c_0 Bool)

(assert (= x_0 3))
(assert (= c_0 (< x_0 5)))
(assert (=> c_0 (= y_0 (+ x_0 1))))
(assert (=> (not c_0) (= y_1 (- x_0 1))))
(assert (= y_2 (ite c_0 y_0 y_1)))
(assert (not (> y_2 0)))
(check-sat)
(get-model)`;

  const renderTabContent = () => {
    switch (activeTab) {
      case 0: // SSA Form
        return (
          <SyntaxHighlighter 
            language="javascript" 
            style={vs2015}
            customStyle={{ background: '#1e1e1e', height: '100%', borderRadius: '0.375rem' }}
          >
            {ssaExample}
          </SyntaxHighlighter>
        );
      case 1: // SMT Constraints
        return (
          <SyntaxHighlighter 
            language="lisp" 
            style={vs2015}
            customStyle={{ background: '#1e1e1e', height: '100%', borderRadius: '0.375rem' }}
          >
            {smtExample}
          </SyntaxHighlighter>
        );
      case 2: // Results
        return (
          <div className="bg-gray-800 h-full rounded-md p-4 overflow-auto">
            <div className="flex items-center space-x-2 text-green-400 mb-4">
              <CheckCircle className="h-5 w-5" />
              <span className="font-medium">Verification Successful</span>
            </div>
            
            <div className="bg-gray-900 rounded-md p-3 mb-4 border border-green-700/30">
              <div className="text-sm font-medium mb-2">Example where condition holds:</div>
              <div className="grid grid-cols-2 gap-2 text-sm">
                <div className="bg-gray-800 p-2 rounded">x = 3</div>
                <div className="bg-gray-800 p-2 rounded">y = 4</div>
              </div>
            </div>
            
            <div className="text-sm text-gray-300 mb-4">
              <p>The assertion <code className="bg-gray-700 px-1 rounded text-blue-300">y {'>'} 0</code> holds for all possible executions of the program.</p>
              <p className="mt-2">Execution trace verified up to depth {unrollDepth}.</p>
            </div>
          </div>
        );
      case 3: // Visualization
        return (
          <div className="bg-gray-800 h-full rounded-md flex items-center justify-center">
            <div className="text-center text-gray-400">
              <div className="w-16 h-16 mx-auto mb-4 text-blue-500">
                <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
                  <circle cx="12" cy="12" r="10" />
                  <path d="M12 16v-4M12 8h.01" />
                </svg>
              </div>
              <p className="text-sm">Control Flow Graph Visualization</p>
              <p className="text-xs mt-1">Interactive graph will appear once analysis is complete</p>
            </div>
          </div>
        );
      default:
        return null;
    }
  };

  return (
    <div className="h-full flex flex-col p-4">
      <div className="flex items-center justify-between mb-4">
        <div className="flex items-center space-x-4">
          <button
            onClick={handleAnalysis}
            disabled={loading}
            className="px-4 py-2 bg-blue-600 hover:bg-blue-700 text-white rounded-md flex items-center space-x-2 disabled:opacity-50"
          >
            {loading ? (
              <Loader className="h-4 w-4 animate-spin" />
            ) : (
              <Play className="h-4 w-4" />
            )}
            <span>{activeMode === 'verification' ? 'Verify Program' : 'Check Equivalence'}</span>
          </button>
          
          <div className="flex items-center space-x-2">
            <label htmlFor="unroll-depth" className="text-sm text-gray-300">Loop Unrolling:</label>
            <select
              id="unroll-depth"
              value={unrollDepth}
              onChange={(e) => setUnrollDepth(Number(e.target.value))}
              className="bg-gray-700 text-sm border border-gray-600 rounded px-2 py-1"
            >
              {[1, 2, 3, 5, 10].map(value => (
                <option key={value} value={value}>{value}</option>
              ))}
            </select>
          </div>
        </div>
        
        {codeMap['single-program'] && (
          <div className="text-sm text-gray-400">
            <span>Program Length: {codeMap['single-program'].split('\n').length} lines</span>
          </div>
        )}
      </div>
      
      <div className="bg-gray-800 flex-1 rounded-md overflow-hidden flex flex-col">
        <div className="border-b border-gray-700">
          <div className="flex">
            {tabs.map((tab, index) => (
              <button
                key={tab}
                onClick={() => setActiveTab(index)}
                className={`px-4 py-2 text-sm relative ${
                  activeTab === index 
                    ? 'text-blue-400' 
                    : 'text-gray-400 hover:text-gray-200'
                }`}
              >
                {tab}
                {activeTab === index && (
                  <motion.div 
                    className="absolute bottom-0 left-0 right-0 h-0.5 bg-blue-500"
                    layoutId="tab-indicator"
                  />
                )}
              </button>
            ))}
          </div>
        </div>
        
        <div className="flex-1 p-4 overflow-hidden">
          <AnimatePresence mode="wait">
            <motion.div
              key={activeTab}
              initial={{ opacity: 0, y: 10 }}
              animate={{ opacity: 1, y: 0 }}
              exit={{ opacity: 0, y: -10 }}
              transition={{ duration: 0.2 }}
              className="h-full"
            >
              {renderTabContent()}
            </motion.div>
          </AnimatePresence>
        </div>
      </div>
    </div>
  );
};

export default AnalysisPanel;