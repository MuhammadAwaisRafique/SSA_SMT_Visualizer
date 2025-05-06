"""
Optimizer for the Formal Methods Analyzer.
This module implements various optimization techniques for SSA form.
"""

from typing import Dict, List, Set, Tuple, Optional, Any, Union
import copy

from ssa_transformer import (
    SSANode, SSAProgram, SSAAssignment, SSAIfStatement, SSAWhileLoop,
    SSAForLoop, SSABinaryOp, SSAVariable, SSAArrayAccess, SSALiteral,
    SSAAssertStatement, PhiFunction
)

class Optimizer:
    """Optimizes SSA form with various techniques."""
    
    def __init__(self):
        self.constants = {}  # Maps variable name_version to constant value
        self.expressions = {}  # Maps expression hash to variable
        self.used_vars = set()  # Set of variables that are used
    
    def optimize(self, program: SSAProgram) -> SSAProgram:
        """Apply all optimization techniques to the program."""
        self.constants = {}
        self.expressions = {}
        self.used_vars = set()
        
        # Find all used variables first (for dead code elimination)
        self._find_used_variables(program)
        
        # Apply optimizations
        optimized_statements = []
        for stmt in program.statements:
            opt_stmt = self._optimize_statement(stmt)
            if opt_stmt:
                if isinstance(opt_stmt, list):
                    optimized_statements.extend(opt_stmt)
                else:
                    optimized_statements.append(opt_stmt)
        
        return SSAProgram(optimized_statements)
    
    def _find_used_variables(self, program: SSAProgram) -> None:
        """Find all variables that are used in assertions or affect assertions."""
        # First pass: mark variables directly used in assertions
        for stmt in reversed(program.statements):
            if isinstance(stmt, SSAAssertStatement):
                self._mark_used_vars_in_expr(stmt.condition)
        
        # Second pass: mark variables that affect used variables
        for stmt in reversed(program.statements):
            self._find_used_vars_in_statement(stmt)
    
    def _find_used_vars_in_statement(self, stmt: SSANode) -> None:
        """Mark variables as used based on their influence on other used variables."""
        if isinstance(stmt, SSAAssignment):
            if self._is_var_used(stmt.variable):
                # If the variable is used, mark all variables in the expression as used
                self._mark_used_vars_in_expr(stmt.expression)
        elif isinstance(stmt, SSAIfStatement):
            # If any variable in the branches is used, then the condition vars are used
            branch_has_used_var = False
            
            for s in stmt.then_branch:
                if self._statement_has_used_var(s):
                    branch_has_used_var = True
                    break
            
            for s in stmt.else_branch:
                if self._statement_has_used_var(s):
                    branch_has_used_var = True
                    break
            
            for phi in stmt.phi_functions:
                if self._is_var_used(phi.variable):
                    branch_has_used_var = True
                    self._mark_used_vars_in_expr(phi.sources[0])
                    self._mark_used_vars_in_expr(phi.sources[1])
            
            if branch_has_used_var:
                self._mark_used_vars_in_expr(stmt.condition)
                
            # Recursively process statements in branches
            for s in stmt.then_branch:
                self._find_used_vars_in_statement(s)
            for s in stmt.else_branch:
                self._find_used_vars_in_statement(s)
        
        elif isinstance(stmt, (SSAWhileLoop, SSAForLoop)):
            # Process loop statements recursively
            if isinstance(stmt, SSAWhileLoop):
                for s in stmt.body:
                    self._find_used_vars_in_statement(s)
            else:  # ForLoop
                self._find_used_vars_in_statement(stmt.init)
                for s in stmt.body:
                    self._find_used_vars_in_statement(s)
                self._find_used_vars_in_statement(stmt.update)
    
    def _statement_has_used_var(self, stmt: SSANode) -> bool:
        """Check if a statement contains any used variables."""
        if isinstance(stmt, SSAAssignment):
            return self._is_var_used(stmt.variable) or self._expr_has_used_var(stmt.expression)
        elif isinstance(stmt, SSAIfStatement):
            if self._expr_has_used_var(stmt.condition):
                return True
            for s in stmt.then_branch:
                if self._statement_has_used_var(s):
                    return True
            for s in stmt.else_branch:
                if self._statement_has_used_var(s):
                    return True
            for phi in stmt.phi_functions:
                if self._is_var_used(phi.variable):
                    return True
            return False
        elif isinstance(stmt, SSAAssertStatement):
            return self._expr_has_used_var(stmt.condition)
        return False
    
    def _is_var_used(self, var: Union[SSAVariable, SSAArrayAccess]) -> bool:
        """Check if a variable is marked as used."""
        if isinstance(var, SSAVariable):
            return str(var) in self.used_vars
        elif isinstance(var, SSAArrayAccess):
            return f"{var.array}_{var.version}" in self.used_vars or self._expr_has_used_var(var.index)
        return False
    
    def _expr_has_used_var(self, expr: SSANode) -> bool:
        """Check if an expression contains any used variables."""
        if isinstance(expr, SSAVariable):
            return str(expr) in self.used_vars
        elif isinstance(expr, SSAArrayAccess):
            array_used = f"{expr.array}_{expr.version}" in self.used_vars
            index_used = self._expr_has_used_var(expr.index)
            return array_used or index_used
        elif isinstance(expr, SSABinaryOp):
            return self._expr_has_used_var(expr.left) or self._expr_has_used_var(expr.right)
        return False
    
    def _mark_used_vars_in_expr(self, expr: SSANode) -> None:
        """Mark all variables in an expression as used."""
        if isinstance(expr, SSAVariable):
            self.used_vars.add(str(expr))
        elif isinstance(expr, SSAArrayAccess):
            self.used_vars.add(f"{expr.array}_{expr.version}")
            self._mark_used_vars_in_expr(expr.index)
        elif isinstance(expr, SSABinaryOp):
            self._mark_used_vars_in_expr(expr.left)
            self._mark_used_vars_in_expr(expr.right)
        elif isinstance(expr, PhiFunction):
            self._mark_used_vars_in_expr(expr.variable)
            for source in expr.sources:
                self._mark_used_vars_in_expr(source)
    
    def _optimize_statement(self, stmt: SSANode) -> Optional[SSANode]:
        """Apply optimizations to a statement."""
        if isinstance(stmt, SSAAssignment):
            return self._optimize_assignment(stmt)
        elif isinstance(stmt, SSAIfStatement):
            return self._optimize_if_statement(stmt)
        elif isinstance(stmt, SSAWhileLoop):
            return self._optimize_while_loop(stmt)
        elif isinstance(stmt, SSAForLoop):
            return self._optimize_for_loop(stmt)
        elif isinstance(stmt, SSAAssertStatement):
            return self._optimize_assert(stmt)
        return stmt
    
    def _optimize_assignment(self, stmt: SSAAssignment) -> Optional[SSAAssignment]:
        """Optimize an assignment statement with constant propagation and CSE."""
        # Dead code elimination
        if not self._is_var_used(stmt.variable):
            return None
        
        # Constant propagation in the expression
        opt_expr = self._optimize_expression(stmt.expression)
        
        # Check if this is a constant assignment
        if isinstance(opt_expr, SSALiteral):
            if isinstance(stmt.variable, SSAVariable):
                self.constants[str(stmt.variable)] = opt_expr.value
        
        # Common subexpression elimination
        if not isinstance(opt_expr, (SSALiteral, SSAVariable)):
            expr_hash = self._hash_expression(opt_expr)
            if expr_hash in self.expressions:
                # Replace with existing variable
                existing_var = self.expressions[expr_hash]
                return SSAAssignment(stmt.variable, existing_var)
            else:
                # Register this expression
                self.expressions[expr_hash] = stmt.variable
        
        return SSAAssignment(stmt.variable, opt_expr)
    
    def _optimize_if_statement(self, stmt: SSAIfStatement) -> SSAIfStatement:
        """Optimize an if statement."""
        # Optimize condition with constant propagation
        opt_condition = self._optimize_expression(stmt.condition)
        
        # Optimize branches
        opt_then = []
        for s in stmt.then_branch:
            opt_s = self._optimize_statement(s)
            if opt_s:
                if isinstance(opt_s, list):
                    opt_then.extend(opt_s)
                else:
                    opt_then.append(opt_s)
        
        opt_else = []
        for s in stmt.else_branch:
            opt_s = self._optimize_statement(s)
            if opt_s:
                if isinstance(opt_s, list):
                    opt_else.extend(opt_s)
                else:
                    opt_else.append(opt_s)
        
        # Optimize phi functions
        opt_phis = []
        for phi in stmt.phi_functions:
            # Only keep phi functions for used variables
            if self._is_var_used(phi.variable):
                # Optimize phi sources
                opt_sources = [
                    self._optimize_expression(phi.sources[0]),
                    self._optimize_expression(phi.sources[1])
                ]
                opt_phis.append(PhiFunction(phi.variable, opt_sources))
        
        # Constant condition optimization
        if isinstance(opt_condition, SSALiteral) and opt_condition.type == "bool":
            if opt_condition.value:
                # Condition is always true, keep only then branch
                result = opt_then
                # Handle phi functions
                for phi in opt_phis:
                    result.append(SSAAssignment(phi.variable, phi.sources[0]))
                return result
            else:
                # Condition is always false, keep only else branch
                result = opt_else
                # Handle phi functions
                for phi in opt_phis:
                    result.append(SSAAssignment(phi.variable, phi.sources[1]))
                return result
        
        return SSAIfStatement(opt_condition, opt_then, opt_else, opt_phis)
    
    def _optimize_while_loop(self, stmt: SSAWhileLoop) -> SSAWhileLoop:
        """Optimize a while loop."""
        # Optimize condition
        opt_condition = self._optimize_expression(stmt.condition)
        
        # Optimize body
        opt_body = []
        for s in stmt.body:
            opt_s = self._optimize_statement(s)
            if opt_s:
                if isinstance(opt_s, list):
                    opt_body.extend(opt_s)
                else:
                    opt_body.append(opt_s)
        
        # Optimize phi functions
        opt_phis = []
        for phi in stmt.phi_functions:
            if self._is_var_used(phi.variable):
                opt_sources = [
                    self._optimize_expression(phi.sources[0]),
                    self._optimize_expression(phi.sources[1])
                ]
                opt_phis.append(PhiFunction(phi.variable, opt_sources))
        
        return SSAWhileLoop(opt_condition, opt_body, opt_phis, stmt.iteration_count)
    
    def _optimize_for_loop(self, stmt: SSAForLoop) -> SSAForLoop:
        """Optimize a for loop."""
        # Optimize initialization, condition, update
        opt_init = self._optimize_statement(stmt.init)
        opt_condition = self._optimize_expression(stmt.condition)
        opt_update = self._optimize_statement(stmt.update)
        
        # Optimize body
        opt_body = []
        for s in stmt.body:
            opt_s = self._optimize_statement(s)
            if opt_s:
                if isinstance(opt_s, list):
                    opt_body.extend(opt_s)
                else:
                    opt_body.append(opt_s)
        
        # Optimize phi functions
        opt_phis = []
        for phi in stmt.phi_functions:
            if self._is_var_used(phi.variable):
                opt_sources = [
                    self._optimize_expression(phi.sources[0]),
                    self._optimize_expression(phi.sources[1])
                ]
                opt_phis.append(PhiFunction(phi.variable, opt_sources))
        
        return SSAForLoop(
            opt_init if not isinstance(opt_init, list) else opt_init[0],
            opt_condition,
            opt_update if not isinstance(opt_update, list) else opt_update[0],
            opt_body,
            opt_phis,
            stmt.iteration_count
        )
    
    def _optimize_assert(self, stmt: SSAAssertStatement) -> SSAAssertStatement:
        """Optimize an assert statement."""
        opt_condition = self._optimize_expression(stmt.condition)
        return SSAAssertStatement(opt_condition)
    
    def _optimize_expression(self, expr: SSANode) -> SSANode:
        """Apply constant propagation and other optimizations to an expression."""
        if isinstance(expr, SSAVariable):
            var_str = str(expr)
            # Check if we have a constant value for this variable
            if var_str in self.constants:
                return SSALiteral(self.constants[var_str], "int" if isinstance(self.constants[var_str], int) else "bool")
            return expr
        elif isinstance(expr, SSAArrayAccess):
            # Optimize array index
            opt_index = self._optimize_expression(expr.index)
            return SSAArrayAccess(expr.array, opt_index, expr.version)
        elif isinstance(expr, SSABinaryOp):
            # Optimize left and right expressions
            opt_left = self._optimize_expression(expr.left)
            opt_right = self._optimize_expression(expr.right)
            
            # If both sides are literals, compute the result
            if isinstance(opt_left, SSALiteral) and isinstance(opt_right, SSALiteral):
                return self._compute_binary_op(expr.op, opt_left, opt_right)
            
            # If one side is a neutral element, simplify
            if expr.op == "+" and isinstance(opt_right, SSALiteral) and opt_right.value == 0:
                return opt_left
            if expr.op == "+" and isinstance(opt_left, SSALiteral) and opt_left.value == 0:
                return opt_right
            if expr.op == "*" and isinstance(opt_right, SSALiteral) and opt_right.value == 1:
                return opt_left
            if expr.op == "*" and isinstance(opt_left, SSALiteral) and opt_left.value == 1:
                return opt_right
            if expr.op == "*" and (
                (isinstance(opt_right, SSALiteral) and opt_right.value == 0) or
                (isinstance(opt_left, SSALiteral) and opt_left.value == 0)
            ):
                return SSALiteral(0, "int")
            
            return SSABinaryOp(expr.op, opt_left, opt_right)
        elif isinstance(expr, SSALiteral):
            return expr
        return expr
    
    def _compute_binary_op(self, op: str, left: SSALiteral, right: SSALiteral) -> SSALiteral:
        """Compute the result of a binary operation on two literals."""
        left_val = left.value
        right_val = right.value
        
        if op == "+":
            return SSALiteral(left_val + right_val, "int")
        elif op == "-":
            return SSALiteral(left_val - right_val, "int")
        elif op == "*":
            return SSALiteral(left_val * right_val, "int")
        elif op == "/":
            # Handle division by zero
            if right_val == 0:
                return SSALiteral(0, "int")  # Default to 0 to avoid errors
            return SSALiteral(left_val // right_val, "int")  # Integer division
        elif op == "==":
            return SSALiteral(left_val == right_val, "bool")
        elif op == "!=":
            return SSALiteral(left_val != right_val, "bool")
        elif op == "<":
            return SSALiteral(left_val < right_val, "bool")
        elif op == "<=":
            return SSALiteral(left_val <= right_val, "bool")
        elif op == ">":
            return SSALiteral(left_val > right_val, "bool")
        elif op == ">=":
            return SSALiteral(left_val >= right_val, "bool")
        
        # Default case (should not happen)
        return SSALiteral(0, "int")
    
    def _hash_expression(self, expr: SSANode) -> str:
        """Create a hash for an expression to identify common subexpressions."""
        if isinstance(expr, SSABinaryOp):
            left_hash = self._hash_expression(expr.left)
            right_hash = self._hash_expression(expr.right)
            return f"({expr.op} {left_hash} {right_hash})"
        elif isinstance(expr, SSAVariable):
            return str(expr)
        elif isinstance(expr, SSAArrayAccess):
            index_hash = self._hash_expression(expr.index)
            return f"{expr.array}[{index_hash}]_{expr.version}"
        elif isinstance(expr, SSALiteral):
            return str(expr.value)
        return str(expr)