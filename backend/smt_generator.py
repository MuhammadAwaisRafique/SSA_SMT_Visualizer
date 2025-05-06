"""
SMT Generator for the Formal Methods Analyzer.
This module generates SMT constraints from SSA form.
"""

from typing import Dict, List, Set, Tuple, Optional, Any
import copy

from parser import ASTNode
from ssa_transformer import (
    SSANode, SSAProgram, SSAAssignment, SSAIfStatement, SSAWhileLoop,
    SSAForLoop, SSABinaryOp, SSAVariable, SSAArrayAccess, SSALiteral,
    SSAAssertStatement, PhiFunction
)

class SMTGenerator:
    """Generates SMT constraints from SSA form."""
    
    def __init__(self):
        self.constraints = []
        self.array_vars = set()
        self.int_vars = set()
        self.bool_vars = set()
        self.var_declarations = []
    
    def generate_verification_constraints(self, program: SSAProgram) -> str:
        """Generate SMT constraints for program verification."""
        self.constraints = []
        self.array_vars = set()
        self.int_vars = set()
        self.bool_vars = set()
        self.var_declarations = []
        
        # Process all statements to collect constraints
        for stmt in program.statements:
            self._process_statement(stmt)
        
        # Combine all constraints into SMT-LIB format
        smt_code = self._format_smt_code()
        return smt_code
    
    def generate_equivalence_constraints(self, program1: SSAProgram, program2: SSAProgram) -> str:
        """Generate SMT constraints for program equivalence checking."""
        # First, generate constraints for each program
        self.constraints = []
        self.array_vars = set()
        self.int_vars = set()
        self.bool_vars = set()
        self.var_declarations = []
        
        # Add prefix to variables in program1 to avoid name collisions
        program1_constraints = []
        for stmt in program1.statements:
            self._process_statement(stmt, prefix="p1_")
        program1_constraints = self.constraints.copy()
        
        # Add prefix to variables in program2
        self.constraints = []
        for stmt in program2.statements:
            self._process_statement(stmt, prefix="p2_")
        program2_constraints = self.constraints.copy()
        
        # Combine constraints
        self.constraints = program1_constraints + program2_constraints
        
        # Add equivalence constraints for output variables
        # We assume the output variables are the ones used in assertions
        output_vars1 = self._find_assertion_variables(program1, prefix="p1_")
        output_vars2 = self._find_assertion_variables(program2, prefix="p2_")
        
        # Generate equivalence constraint
        equiv_constraint = []
        for var1, var2 in zip(output_vars1, output_vars2):
            equiv_constraint.append(f"(assert (= {var1} {var2}))")
        
        # Negate the equivalence to check for counterexamples
        if equiv_constraint:
            self.constraints.append(f"(assert (not (and {' '.join(equiv_constraint)})))")
        
        # Combine all constraints into SMT-LIB format
        smt_code = self._format_smt_code()
        return smt_code
    
    def _find_assertion_variables(self, program: SSAProgram, prefix: str = "") -> List[str]:
        """Find variables used in assertions."""
        output_vars = []
        
        for stmt in program.statements:
            if isinstance(stmt, SSAAssertStatement):
                vars_in_assertion = self._extract_variables_from_expression(stmt.condition, prefix)
                output_vars.extend(vars_in_assertion)
        
        return output_vars
    
    def _extract_variables_from_expression(self, expr: SSANode, prefix: str = "") -> List[str]:
        """Extract all variables from an expression."""
        if isinstance(expr, SSAVariable):
            return [f"{prefix}{expr}"]
        elif isinstance(expr, SSAArrayAccess):
            index_vars = self._extract_variables_from_expression(expr.index, prefix)
            return [f"{prefix}{expr}"] + index_vars
        elif isinstance(expr, SSABinaryOp):
            left_vars = self._extract_variables_from_expression(expr.left, prefix)
            right_vars = self._extract_variables_from_expression(expr.right, prefix)
            return left_vars + right_vars
        else:
            return []
    
    def _process_statement(self, stmt: SSANode, prefix: str = "") -> None:
        """Process a statement and add constraints."""
        if isinstance(stmt, SSAAssignment):
            self._process_assignment(stmt, prefix)
        elif isinstance(stmt, SSAIfStatement):
            self._process_if_statement(stmt, prefix)
        elif isinstance(stmt, SSAWhileLoop):
            # Unrolled loops are already transformed into if statements
            pass
        elif isinstance(stmt, SSAForLoop):
            # Unrolled loops are already transformed into if statements
            pass
        elif isinstance(stmt, SSAAssertStatement):
            self._process_assert(stmt, prefix)
    
    def _process_assignment(self, stmt: SSAAssignment, prefix: str = "") -> None:
        """Process an assignment statement."""
        lhs = self._format_variable(stmt.variable, prefix)
        rhs = self._format_expression(stmt.expression, prefix)
        
        # Track variable type
        if isinstance(stmt.variable, SSAVariable):
            self.int_vars.add(f"{prefix}{stmt.variable}")
        elif isinstance(stmt.variable, SSAArrayAccess):
            self.array_vars.add(f"{prefix}{stmt.variable.array}")
            # Get index variable type
            if isinstance(stmt.variable.index, SSAVariable):
                self.int_vars.add(f"{prefix}{stmt.variable.index}")
        
        self.constraints.append(f"(assert (= {lhs} {rhs}))")
    
    def _process_if_statement(self, stmt: SSAIfStatement, prefix: str = "") -> None:
        """Process an if statement."""
        condition = self._format_expression(stmt.condition, prefix)
        
        # Add a boolean variable for the condition
        cond_var = f"c_{len(self.constraints)}"
        self.bool_vars.add(cond_var)
        self.constraints.append(f"(assert (= {cond_var} {condition}))")
        
        # Process then branch
        for s in stmt.then_branch:
            self._process_statement(s, prefix)
            # Add implication: if condition then statement
            if isinstance(s, SSAAssignment):
                lhs = self._format_variable(s.variable, prefix)
                rhs = self._format_expression(s.expression, prefix)
                self.constraints.append(f"(assert (=> {cond_var} (= {lhs} {rhs})))")
        
        # Process else branch
        for s in stmt.else_branch:
            self._process_statement(s, prefix)
            # Add implication: if not condition then statement
            if isinstance(s, SSAAssignment):
                lhs = self._format_variable(s.variable, prefix)
                rhs = self._format_expression(s.expression, prefix)
                self.constraints.append(f"(assert (=> (not {cond_var}) (= {lhs} {rhs})))")
        
        # Process phi functions
        for phi in stmt.phi_functions:
            result_var = self._format_variable(phi.variable, prefix)
            source1 = self._format_variable(phi.sources[0], prefix)
            source2 = self._format_variable(phi.sources[1], prefix)
            self.constraints.append(f"(assert (= {result_var} (ite {cond_var} {source1} {source2})))")
    
    def _process_assert(self, stmt: SSAAssertStatement, prefix: str = "") -> None:
        """Process an assert statement."""
        condition = self._format_expression(stmt.condition, prefix)
        # Add the negation of the assertion to find counterexamples
        self.constraints.append(f"(assert (not {condition}))")
    
    def _format_variable(self, var: SSANode, prefix: str = "") -> str:
        """Format a variable for SMT code."""
        if isinstance(var, SSAVariable):
            var_name = f"{prefix}{var}"
            self.int_vars.add(var_name)
            return var_name
        elif isinstance(var, SSAArrayAccess):
            array_name = f"{prefix}{var.array}"
            index = self._format_expression(var.index, prefix)
            self.array_vars.add(array_name)
            return f"(select {array_name} {index})"
        else:
            raise TypeError(f"Unsupported variable type: {type(var)}")
    
    def _format_expression(self, expr: SSANode, prefix: str = "") -> str:
        """Format an expression for SMT code."""
        if isinstance(expr, SSABinaryOp):
            left = self._format_expression(expr.left, prefix)
            right = self._format_expression(expr.right, prefix)
            
            # Map operators to SMT
            op_map = {
                "+": "+",
                "-": "-",
                "*": "*",
                "/": "div",
                "==": "=",
                "!=": "distinct",
                "<": "<",
                "<=": "<=",
                ">": ">",
                ">=": ">=",
            }
            
            smt_op = op_map.get(expr.op, expr.op)
            return f"({smt_op} {left} {right})"
        elif isinstance(expr, SSAVariable):
            var_name = f"{prefix}{expr}"
            self.int_vars.add(var_name)
            return var_name
        elif isinstance(expr, SSAArrayAccess):
            array_name = f"{prefix}{expr.array}"
            index = self._format_expression(expr.index, prefix)
            self.array_vars.add(array_name)
            return f"(select {array_name} {index})"
        elif isinstance(expr, SSALiteral):
            if expr.type == "int":
                return str(expr.value)
            elif expr.type == "bool":
                return "true" if expr.value else "false"
            else:
                return str(expr.value)
        else:
            raise TypeError(f"Unsupported expression type: {type(expr)}")
    
    def _format_smt_code(self) -> str:
        """Format all constraints into SMT-LIB code."""
        declarations = []
        
        # Declare int variables
        for var in self.int_vars:
            declarations.append(f"(declare-const {var} Int)")
        
        # Declare bool variables
        for var in self.bool_vars:
            declarations.append(f"(declare-const {var} Bool)")
        
        # Declare array variables
        for var in self.array_vars:
            declarations.append(f"(declare-const {var} (Array Int Int))")
        
        # Combine all parts
        smt_code = "\n".join(declarations + self.constraints + ["(check-sat)", "(get-model)"])
        return smt_code