import React, { createContext, useContext, ReactNode, useState } from 'react';

type AnalysisMode = 'verification' | 'equivalence';

interface LayoutContextType {
  activeMode: AnalysisMode;
  setActiveMode: (mode: AnalysisMode) => void;
}

const LayoutContext = createContext<LayoutContextType | undefined>(undefined);

export const LayoutProvider: React.FC<{ children: ReactNode }> = ({ children }) => {
  const [activeMode, setActiveMode] = useState<AnalysisMode>('verification');

  return (
    <LayoutContext.Provider value={{ activeMode, setActiveMode }}>
      {children}
    </LayoutContext.Provider>
  );
};

export const useLayoutContext = (): LayoutContextType => {
  const context = useContext(LayoutContext);
  if (context === undefined) {
    throw new Error('useLayoutContext must be used within a LayoutProvider');
  }
  return context;
};