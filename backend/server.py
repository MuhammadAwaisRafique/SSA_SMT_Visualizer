from flask import Flask, request, jsonify
from flask_cors import CORS
import sys
import os
import json

# Add parser and analyzer modules
sys.path.append(os.path.dirname(os.path.abspath(__file__)))
from parser import Parser
from ssa_transformer import SSATransformer
from smt_generator import SMTGenerator
from optimizer import Optimizer
from visualizer import Visualizer
from z3_interface import Z3Interface

app = Flask(__name__)
CORS(app)

@app.route('/api/analyze', methods=['POST'])
def analyze():
    data = request.json
    mode = data.get('mode', 'verification')
    code = data.get('code', '')
    second_code = data.get('secondCode', '') if mode == 'equivalence' else None
    unroll_depth = data.get('unrollDepth', 3)
    
    try:
        # Parse the program(s)
        parser = Parser()
        parsed_program = parser.parse(code)
        parsed_program2 = parser.parse(second_code) if second_code else None
        
        # Transform to SSA
        ssa_transformer = SSATransformer()
        ssa_result = ssa_transformer.transform(parsed_program, unroll_depth)
        ssa_result2 = ssa_transformer.transform(parsed_program2, unroll_depth) if parsed_program2 else None
        
        # Optimize SSA (optional)
        optimizer = Optimizer()
        optimized_ssa = optimizer.optimize(ssa_result)
        optimized_ssa2 = optimizer.optimize(ssa_result2) if ssa_result2 else None
        
        # Generate control flow graph
        visualizer = Visualizer()
        cfg = visualizer.generate_cfg(parsed_program)
        cfg2 = visualizer.generate_cfg(parsed_program2) if parsed_program2 else None
        
        # Generate SMT constraints
        smt_generator = SMTGenerator()
        if mode == 'verification':
            smt_constraints = smt_generator.generate_verification_constraints(optimized_ssa)
        else:
            smt_constraints = smt_generator.generate_equivalence_constraints(optimized_ssa, optimized_ssa2)
        
        # Run Z3 solver
        z3_interface = Z3Interface()
        verification_result = z3_interface.solve(smt_constraints)
        
        # Generate counterexamples if needed
        counterexamples = []
        if not verification_result['satisfiable']:
            counterexamples = z3_interface.generate_counterexamples(smt_constraints)
        
        # Format the results
        formatted_ssa = visualizer.format_ssa(optimized_ssa)
        formatted_ssa2 = visualizer.format_ssa(optimized_ssa2) if optimized_ssa2 else None
        
        response = {
            'success': True,
            'ssaForm': formatted_ssa,
            'ssaForm2': formatted_ssa2 if formatted_ssa2 else None,
            'smtConstraints': smt_constraints,
            'verificationResult': verification_result,
            'counterexamples': counterexamples,
            'cfg': cfg,
            'cfg2': cfg2 if cfg2 else None,
        }
        
        return jsonify(response)
    
    except Exception as e:
        return jsonify({
            'success': False,
            'error': str(e)
        }), 400

@app.route('/api/examples', methods=['GET'])
def get_examples():
    examples = {
        'if-else': '''x := 3;
if (x < 5) {
  y := x + 1;
} else {
  y := x - 1;
}
assert(y > 0);''',
        'loop': '''x := 0;
while (x < 4) {
  x := x + 1;
}
assert(x == 4);''',
        'bubble-sort': '''for (i := 0; i < n; i := i + 1) {
  for (j := 0; j < n - i - 1; j := j + 1) {
    if (arr[j] > arr[j+1]) {
      temp := arr[j];
      arr[j] := arr[j+1];
      arr[j+1] := temp;
    }
  }
}
assert(arr is sorted);''',
    }
    
    return jsonify(examples)

if __name__ == '__main__':
    app.run(debug=True, port=5000)