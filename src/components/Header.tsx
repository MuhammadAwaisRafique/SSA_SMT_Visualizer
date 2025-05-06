import React from 'react';
import { BookOpen, Code, GitCompare, Settings } from 'lucide-react';
import { useLayoutContext } from '../context/LayoutContext';

const Header: React.FC = () => {
  const { activeMode, setActiveMode } = useLayoutContext();

  return (
    <header className="bg-gray-800 border-b border-gray-700">
      <div className="container mx-auto px-4 py-3 flex items-center justify-between">
        <div className="flex items-center space-x-2">
          <Code className="h-6 w-6 text-blue-400" />
          <h1 className="text-xl font-bold">Formal Methods Analyzer</h1>
        </div>
        
        <div className="flex items-center space-x-2">
          <button
            onClick={() => setActiveMode('verification')}
            className={`px-3 py-1.5 rounded-md flex items-center space-x-1.5 ${
              activeMode === 'verification' 
                ? 'bg-blue-700 text-white' 
                : 'text-gray-300 hover:bg-gray-700'
            }`}
          >
            <BookOpen className="h-4 w-4" />
            <span>Verification</span>
          </button>
          
          <button
            onClick={() => setActiveMode('equivalence')}
            className={`px-3 py-1.5 rounded-md flex items-center space-x-1.5 ${
              activeMode === 'equivalence' 
                ? 'bg-blue-700 text-white' 
                : 'text-gray-300 hover:bg-gray-700'
            }`}
          >
            <GitCompare className="h-4 w-4" />
            <span>Equivalence</span>
          </button>
          
          <button className="ml-2 p-1.5 text-gray-400 hover:text-white hover:bg-gray-700 rounded-md">
            <Settings className="h-5 w-5" />
          </button>
        </div>
      </div>
    </header>
  );
};

export default Header;