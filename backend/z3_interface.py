"""
Z3 Interface for the Formal Methods Analyzer.
This module provides an interface to the Z3 SMT solver.
"""

from typing import Dict, List, Any
import subprocess
import re
import json
import tempfile
import os

class Z3Interface:
    """Interface to the Z3 SMT solver."""
    
    def __init__(self):
        self.model = None
        self.timeout = 10000  # milliseconds
    
    def solve(self, smt_constraints: str) -> Dict[str, Any]:
        """Solve the SMT constraints using Z3 and return the result."""
        # Write constraints to a temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as tmp:
            tmp.write(smt_constraints)
            tmp_filename = tmp.name
        
        try:
            # Run Z3 as a subprocess
            cmd = ['z3', '-smt2', '-t:' + str(self.timeout), tmp_filename]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=self.timeout/1000)
            
            # Parse the output
            output = result.stdout.strip()
            
            if "unsat" in output:
                # Verification successful or no counterexample
                return {
                    'satisfiable': False,
                    'result': 'UNSAT',
                    'message': 'No counterexample found. The property holds.'
                }
            elif "sat" in output:
                # Verification failed or counterexample found
                self.model = self._parse_z3_model(output)
                return {
                    'satisfiable': True,
                    'result': 'SAT',
                    'message': 'Counterexample found. The property may not hold.',
                    'model': self.model
                }
            else:
                # Unknown or timeout
                return {
                    'satisfiable': None,
                    'result': 'UNKNOWN',
                    'message': 'The solver could not determine if the property holds.',
                    'output': output
                }
        
        except subprocess.TimeoutExpired:
            return {
                'satisfiable': None,
                'result': 'TIMEOUT',
                'message': f'The solver timed out after {self.timeout} ms.'
            }
        except Exception as e:
            return {
                'satisfiable': None,
                'result': 'ERROR',
                'message': str(e)
            }
        finally:
            # Clean up the temporary file
            if os.path.exists(tmp_filename):
                os.remove(tmp_filename)
    
    def generate_counterexamples(self, smt_constraints: str) -> List[Dict[str, Any]]:
        """Generate multiple counterexamples by solving with added constraints."""
        counterexamples = []
        
        # Use the existing model if available
        if self.model:
            counterexamples.append(self.model)
        
        # Try to find more counterexamples by blocking the current model
        for _ in range(2):  # Find up to 2 more counterexamples
            if not self.model:
                break
                
            # Add constraints to block the current model
            blocking_constraints = self._generate_blocking_constraints()
            new_constraints = smt_constraints + "\n\n" + blocking_constraints
            
            # Solve again
            result = self.solve(new_constraints)
            if result['satisfiable']:
                counterexamples.append(result['model'])
            else:
                break
        
        return counterexamples
    
    def _generate_blocking_constraints(self) -> str:
        """Generate constraints to block the current model."""
        if not self.model:
            return ""
        
        conditions = []
        for var, value in self.model.items():
            if isinstance(value, int):
                conditions.append(f"(not (= {var} {value}))")
            elif isinstance(value, str) and value.lower() in ["true", "false"]:
                conditions.append(f"(not (= {var} {value.lower()}))")
        
        if conditions:
            return "(assert " + "(or " + " ".join(conditions) + "))"
        
        return ""
    
    def _parse_z3_model(self, output: str) -> Dict[str, Any]:
        """Parse the Z3 model from the output string."""
        model = {}
        
        # Extract the model section
        model_match = re.search(r'model\s*\n(.*?)(\n\)|$)', output, re.DOTALL)
        if not model_match:
            return model
            
        model_str = model_match.group(1)
        
        # Extract variable definitions
        var_pattern = r'define-fun\s+(\w+[_\d]*)\s+\(\)\s+(\w+)\s+(.*?)\)'
        for match in re.finditer(var_pattern, model_str, re.DOTALL):
            var_name = match.group(1)
            var_type = match.group(2)
            var_value = match.group(3).strip()
            
            # Convert value based on type
            if var_type == 'Int':
                try:
                    model[var_name] = int(var_value)
                except ValueError:
                    model[var_name] = var_value
            elif var_type == 'Bool':
                model[var_name] = var_value
            else:
                model[var_name] = var_value
        
        return model