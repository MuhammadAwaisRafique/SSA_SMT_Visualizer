import React from 'react';
import CodeMirror from '@uiw/react-codemirror';
import { vscodeDark } from '@uiw/codemirror-theme-vscode';
import { javascript } from '@codemirror/lang-javascript';
import { useAnalysisStore } from '../store/analysisStore';

interface CodeEditorProps {
  id: string;
  label: string;
  placeholder?: string;
}

const CodeEditor: React.FC<CodeEditorProps> = ({ id, label, placeholder }) => {
  const { setCode } = useAnalysisStore();

  const handleChange = (value: string) => {
    setCode(id, value);
  };

  // Sample program for if-else
  const sampleProgram = `// Example program - If-Else
x := 3;
if (x < 5) {
  y := x + 1;
} else {
  y := x - 1;
}
assert(y > 0);`;

  return (
    <div className="h-full flex flex-col">
      <div className="text-sm text-gray-300 mb-2 flex justify-between items-center">
        <span>{label}</span>
        <div className="space-x-2">
          <button 
            className="px-2 py-1 text-xs bg-gray-700 hover:bg-gray-600 rounded"
            onClick={() => handleChange(sampleProgram)}
          >
            Load Example
          </button>
        </div>
      </div>
      <div className="flex-1 overflow-hidden border border-gray-700 rounded-md">
        <CodeMirror
          value=""
          height="100%"
          placeholder={placeholder}
          theme={vscodeDark}
          extensions={[javascript()]}
          onChange={handleChange}
          basicSetup={{
            lineNumbers: true,
            highlightActiveLine: true,
            highlightSelectionMatches: true,
            autocompletion: true,
          }}
        />
      </div>
    </div>
  );
};

export default CodeEditor;