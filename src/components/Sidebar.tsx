import React, { useState } from 'react';
import { ChevronRight, Code, FileCode, FileCog, Settings, Share2 } from 'lucide-react';
import { motion } from 'framer-motion';

const Sidebar: React.FC = () => {
  const [collapsed, setCollapsed] = useState(false);
  
  const sidebarVariants = {
    expanded: { width: '240px' },
    collapsed: { width: '56px' }
  };
  
  const examplePrograms = [
    { name: 'If-Else Example', id: 'if-else' },
    { name: 'Loop Example', id: 'loop' },
    { name: 'Bubble Sort', id: 'bubble-sort' },
    { name: 'Selection Sort', id: 'selection-sort' },
    { name: 'Insertion Sort', id: 'insertion-sort' }
  ];

  return (
    <motion.div
      className="bg-gray-800 border-r border-gray-700 h-full flex flex-col"
      initial="expanded"
      animate={collapsed ? 'collapsed' : 'expanded'}
      variants={sidebarVariants}
      transition={{ duration: 0.3 }}
    >
      <div className="flex items-center justify-between p-3 border-b border-gray-700">
        {!collapsed && <h2 className="font-medium">Explorer</h2>}
        <button 
          onClick={() => setCollapsed(!collapsed)}
          className="p-1 rounded-md hover:bg-gray-700"
        >
          <ChevronRight 
            className={`h-5 w-5 transition-transform ${collapsed ? 'rotate-180' : ''}`} 
          />
        </button>
      </div>
      
      <div className="overflow-y-auto flex-1">
        <div className="p-2">
          {!collapsed && (
            <div className="text-sm font-medium text-gray-400 px-2 py-1.5">
              Example Programs
            </div>
          )}
          
          {examplePrograms.map(program => (
            <button 
              key={program.id}
              className={`w-full flex items-center space-x-2 px-2 py-1.5 rounded-md hover:bg-gray-700 text-left ${
                collapsed ? 'justify-center' : ''
              }`}
            >
              <FileCode className="h-4 w-4 text-blue-400 flex-shrink-0" />
              {!collapsed && <span className="text-sm truncate">{program.name}</span>}
            </button>
          ))}
        </div>
        
        {!collapsed && (
          <div className="p-2">
            <div className="text-sm font-medium text-gray-400 px-2 py-1.5">
              Tools
            </div>
            
            <button className="w-full flex items-center space-x-2 px-2 py-1.5 rounded-md hover:bg-gray-700 text-left">
              <FileCog className="h-4 w-4 text-green-400" />
              <span className="text-sm">Parser Settings</span>
            </button>
            
            <button className="w-full flex items-center space-x-2 px-2 py-1.5 rounded-md hover:bg-gray-700 text-left">
              <Code className="h-4 w-4 text-purple-400" />
              <span className="text-sm">SSA Options</span>
            </button>
            
            <button className="w-full flex items-center space-x-2 px-2 py-1.5 rounded-md hover:bg-gray-700 text-left">
              <Share2 className="h-4 w-4 text-orange-400" />
              <span className="text-sm">Export Results</span>
            </button>
          </div>
        )}
      </div>
      
      <div className="p-2 border-t border-gray-700">
        <button className={`w-full flex items-center px-2 py-1.5 rounded-md hover:bg-gray-700 text-left ${
          collapsed ? 'justify-center' : 'space-x-2'
        }`}>
          <Settings className="h-4 w-4 text-gray-400" />
          {!collapsed && <span className="text-sm">Settings</span>}
        </button>
      </div>
    </motion.div>
  );
};

export default Sidebar;