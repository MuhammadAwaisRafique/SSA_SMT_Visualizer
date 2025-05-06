import { create } from 'zustand';

interface AnalysisState {
  codeMap: Record<string, string>;
  ssaForm: string;
  smtConstraints: string;
  results: any;
  loading: boolean;
  error: string | null;
  setCode: (id: string, code: string) => void;
  setSsaForm: (ssa: string) => void;
  setSmtConstraints: (smt: string) => void;
  setResults: (results: any) => void;
  setLoading: (loading: boolean) => void;
  setError: (error: string | null) => void;
}

export const useAnalysisStore = create<AnalysisState>((set) => ({
  codeMap: {},
  ssaForm: '',
  smtConstraints: '',
  results: null,
  loading: false,
  error: null,
  setCode: (id, code) => set((state) => ({ 
    codeMap: { ...state.codeMap, [id]: code } 
  })),
  setSsaForm: (ssa) => set({ ssaForm: ssa }),
  setSmtConstraints: (smt) => set({ smtConstraints: smt }),
  setResults: (results) => set({ results }),
  setLoading: (loading) => set({ loading }),
  setError: (error) => set({ error }),
}));