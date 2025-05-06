import React from 'react';
import { LayoutProvider } from './context/LayoutContext';
import MainLayout from './layouts/MainLayout';
import Header from './components/Header';

function App() {
  return (
    <div className="min-h-screen bg-gray-900 text-gray-100 flex flex-col">
      <LayoutProvider>
        <Header />
        <MainLayout />
      </LayoutProvider>
    </div>
  );
}

export default App;