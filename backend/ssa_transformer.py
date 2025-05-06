"""
SSA Transformer for the Formal Methods Analyzer.
This module transforms the AST into Static Single Assignment (SSA) form.
"""

from typing import Dict, List, Set, Tuple, Optional, Any
import copy

from parser import (
    ASTNode, Program, Assignment, IfStatement, WhileLoop, 
    ForLoop, BinaryOp, Variable, ArrayAccess, Literal, AssertStatement
)

class SSAVariable:
    """Represents a variable in SSA form."""
    def __init__(self, name, version):
        self.name = name
        self.version = version
    
    def __str__(self):
        return f"{self.name}_{self.version}"

class PhiFunction:
    """Represents a phi function in SSA form."""
    def __init__(self, variable, sources):
        self.variable = variable
        self.sources = sources
    
    def __str__(self):
        sources_str = ", ".join(str(s) for s in self.sources)
        return f"{self.variable} := PHI({sources_str})"

class SSANode:
    """Base class for SSA nodes."""
    pass

class SSAProgram(SSANode):
    """Represents a complete program in SSA form."""
    def __init__(self, statements):
        self.statements = statements

class SSAAssignment(SSANode):
    """Represents an assignment in SSA form."""
    def __init__(self, variable, expression):
        self.variable = variable
        self.expression = expression

class SSAIfStatement(SSANode):
    """Represents an if-else statement in SSA form."""
    def __init__(self, condition, then_branch, else_branch, phi_functions):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch
        self.phi_functions = phi_functions

class SSAWhileLoop(SSANode):
    """Represents a while loop in SSA form."""
    def __init__(self, condition, body, phi_functions, iteration_count):
        self.condition = condition
        self.body = body
        self.phi_functions = phi_functions
        self.iteration_count = iteration_count  # For loop unrolling

class SSAForLoop(SSANode):
    """Represents a for loop in SSA form."""
    def __init__(self, init, condition, update, body, phi_functions, iteration_count):
        self.init = init
        self.condition = condition
        self.update = update
        self.body = body
        self.phi_functions = phi_functions
        self.iteration_count = iteration_count  # For loop unrolling

class SSABinaryOp(SSANode):
    """Represents a binary operation in SSA form."""
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

class SSAVariable(SSANode):
    """Represents a variable reference in SSA form."""
    def __init__(self, name, version):
        self.name = name
        self.version = version
    
    def __str__(self):
        return f"{self.name}_{self.version}"

class SSAArrayAccess(SSANode):
    """Represents array access in SSA form."""
    def __init__(self, array, index, version):
        self.array = array
        self.index = index
        self.version = version
    
    def __str__(self):
        return f"{self.array}[{self.index}]_{self.version}"

class SSALiteral(SSANode):
    """Represents a literal value in SSA form."""
    def __init__(self, value, type_name):
        self.value = value
        self.type = type_name

class SSAAssertStatement(SSANode):
    """Represents an assertion in SSA form."""
    def __init__(self, condition):
        self.condition = condition

class SSATransformer:
    """Transforms AST into SSA form."""
    
    def __init__(self):
        self.var_versions = {}  # Maps variable names to their current version
        self.phi_functions = {}  # Maps variable names to their phi functions
        self.unroll_depth = 3  # Default unroll depth
    
    def transform(self, program: Program, unroll_depth: int = 3) -> SSAProgram:
        """Transform the program into SSA form."""
        self.var_versions = {}
        self.phi_functions = {}
        self.unroll_depth = unroll_depth
        
        ssa_statements = []
        for stmt in program.statements:
            ssa_stmt = self._transform_statement(stmt)
            if isinstance(ssa_stmt, list):
                ssa_statements.extend(ssa_stmt)
            else:
                ssa_statements.append(ssa_stmt)
        
        return SSAProgram(ssa_statements)
    
    def _transform_statement(self, stmt: ASTNode) -> SSANode:
        """Transform a statement into SSA form."""
        if isinstance(stmt, Assignment):
            return self._transform_assignment(stmt)
        elif isinstance(stmt, IfStatement):
            return self._transform_if_statement(stmt)
        elif isinstance(stmt, WhileLoop):
            return self._transform_while_loop(stmt)
        elif isinstance(stmt, ForLoop):
            return self._transform_for_loop(stmt)
        elif isinstance(stmt, AssertStatement):
            return self._transform_assert(stmt)
        else:
            raise TypeError(f"Unsupported statement type: {type(stmt)}")
    
    def _transform_assignment(self, stmt: Assignment) -> SSAAssignment:
        """Transform an assignment into SSA form."""
        ssa_expr = self._transform_expression(stmt.expression)
        
        if isinstance(stmt.variable, Variable):
            var_name = stmt.variable.name
            self._increment_version(var_name)
            ssa_var = SSAVariable(var_name, self.var_versions[var_name])
            return SSAAssignment(ssa_var, ssa_expr)
        elif isinstance(stmt.variable, ArrayAccess):
            array_name = stmt.variable.array.name
            ssa_index = self._transform_expression(stmt.variable.index)
            self._increment_version(array_name)
            ssa_var = SSAArrayAccess(array_name, ssa_index, self.var_versions[array_name])
            return SSAAssignment(ssa_var, ssa_expr)
        else:
            raise TypeError(f"Unsupported variable type: {type(stmt.variable)}")
    
    def _transform_if_statement(self, stmt: IfStatement) -> SSAIfStatement:
        """Transform an if statement into SSA form."""
        condition = self._transform_expression(stmt.condition)
        
        # Save current variable versions
        saved_versions = self.var_versions.copy()
        
        # Transform then branch
        then_statements = []
        for s in stmt.then_branch:
            ssa_s = self._transform_statement(s)
            if isinstance(ssa_s, list):
                then_statements.extend(ssa_s)
            else:
                then_statements.append(ssa_s)
        
        # Save then branch variable versions
        then_versions = self.var_versions.copy()
        
        # Restore versions for else branch
        self.var_versions = saved_versions.copy()
        
        # Transform else branch
        else_statements = []
        if stmt.else_branch:
            for s in stmt.else_branch:
                ssa_s = self._transform_statement(s)
                if isinstance(ssa_s, list):
                    else_statements.extend(ssa_s)
                else:
                    else_statements.append(ssa_s)
        
        # Create phi functions for variables modified in either branch
        phi_functions = []
        for var_name in set(then_versions.keys()) | set(self.var_versions.keys()):
            then_ver = then_versions.get(var_name, saved_versions.get(var_name, 0))
            else_ver = self.var_versions.get(var_name, saved_versions.get(var_name, 0))
            
            if then_ver != saved_versions.get(var_name, 0) or else_ver != saved_versions.get(var_name, 0):
                self._increment_version(var_name)
                then_var = SSAVariable(var_name, then_ver)
                else_var = SSAVariable(var_name, else_ver)
                phi_var = SSAVariable(var_name, self.var_versions[var_name])
                phi_functions.append(PhiFunction(phi_var, [then_var, else_var]))
        
        return SSAIfStatement(condition, then_statements, else_statements, phi_functions)
    
    def _transform_while_loop(self, stmt: WhileLoop) -> List[SSANode]:
        """Transform a while loop into SSA form with unrolling."""
        # We'll unroll the loop up to unroll_depth
        result_statements = []
        
        # Initial loop condition check
        condition = self._transform_expression(stmt.condition)
        
        # Save versions before the loop
        pre_loop_versions = self.var_versions.copy()
        
        # Unroll the loop
        for i in range(self.unroll_depth):
            # Create an if statement for each potential iteration
            then_body = []
            
            # Transform loop body
            for s in stmt.body:
                ssa_s = self._transform_statement(s)
                if isinstance(ssa_s, list):
                    then_body.extend(ssa_s)
                else:
                    then_body.append(ssa_s)
            
            # Update condition after the body (for next iteration)
            next_condition = self._transform_expression(stmt.condition)
            
            # Create if statement for this iteration
            if_stmt = SSAIfStatement(
                condition=condition,
                then_branch=then_body,
                else_branch=[],  # No else branch for unrolled loop
                phi_functions=[]  # Phi functions handled separately
            )
            
            result_statements.append(if_stmt)
            condition = next_condition
        
        # Create phi functions for the loop
        phi_functions = []
        for var_name in self.var_versions:
            if self.var_versions[var_name] != pre_loop_versions.get(var_name, 0):
                self._increment_version(var_name)
                pre_loop_var = SSAVariable(var_name, pre_loop_versions.get(var_name, 0))
                post_loop_var = SSAVariable(var_name, self.var_versions[var_name] - 1)
                phi_var = SSAVariable(var_name, self.var_versions[var_name])
                phi_functions.append(PhiFunction(phi_var, [pre_loop_var, post_loop_var]))
        
        # Create a SSAWhileLoop to represent the original structure (for visualization)
        ssa_while = SSAWhileLoop(
            condition=self._transform_expression(stmt.condition),
            body=[self._transform_statement(s) for s in stmt.body],
            phi_functions=phi_functions,
            iteration_count=self.unroll_depth
        )
        
        # For SMT generation, we'll use the unrolled if statements
        return result_statements
    
    def _transform_for_loop(self, stmt: ForLoop) -> List[SSANode]:
        """Transform a for loop into SSA form with unrolling."""
        result_statements = []
        
        # Initialize the loop variable
        init_stmt = self._transform_statement(stmt.init)
        result_statements.append(init_stmt)
        
        # Initial loop condition check
        condition = self._transform_expression(stmt.condition)
        
        # Save versions before the loop
        pre_loop_versions = self.var_versions.copy()
        
        # Unroll the loop
        for i in range(self.unroll_depth):
            # Create an if statement for each potential iteration
            then_body = []
            
            # Transform loop body
            for s in stmt.body:
                ssa_s = self._transform_statement(s)
                if isinstance(ssa_s, list):
                    then_body.extend(ssa_s)
                else:
                    then_body.append(ssa_s)
            
            # Update variable at the end of iteration
            update_stmt = self._transform_statement(stmt.update)
            then_body.append(update_stmt)
            
            # Update condition after the body (for next iteration)
            next_condition = self._transform_expression(stmt.condition)
            
            # Create if statement for this iteration
            if_stmt = SSAIfStatement(
                condition=condition,
                then_branch=then_body,
                else_branch=[],  # No else branch for unrolled loop
                phi_functions=[]  # Phi functions handled separately
            )
            
            result_statements.append(if_stmt)
            condition = next_condition
        
        # Create phi functions for the loop
        phi_functions = []
        for var_name in self.var_versions:
            if self.var_versions[var_name] != pre_loop_versions.get(var_name, 0):
                self._increment_version(var_name)
                pre_loop_var = SSAVariable(var_name, pre_loop_versions.get(var_name, 0))
                post_loop_var = SSAVariable(var_name, self.var_versions[var_name] - 1)
                phi_var = SSAVariable(var_name, self.var_versions[var_name])
                phi_functions.append(PhiFunction(phi_var, [pre_loop_var, post_loop_var]))
        
        # Create a SSAForLoop to represent the original structure (for visualization)
        ssa_for = SSAForLoop(
            init=self._transform_statement(stmt.init),
            condition=self._transform_expression(stmt.condition),
            update=self._transform_statement(stmt.update),
            body=[self._transform_statement(s) for s in stmt.body],
            phi_functions=phi_functions,
            iteration_count=self.unroll_depth
        )
        
        # For SMT generation, we'll use the unrolled if statements
        return result_statements
    
    def _transform_assert(self, stmt: AssertStatement) -> SSAAssertStatement:
        """Transform an assert statement into SSA form."""
        ssa_condition = self._transform_expression(stmt.condition)
        return SSAAssertStatement(ssa_condition)
    
    def _transform_expression(self, expr: ASTNode) -> SSANode:
        """Transform an expression into SSA form."""
        if isinstance(expr, BinaryOp):
            ssa_left = self._transform_expression(expr.left)
            ssa_right = self._transform_expression(expr.right)
            return SSABinaryOp(expr.op, ssa_left, ssa_right)
        elif isinstance(expr, Variable):
            var_name = expr.name
            version = self.var_versions.get(var_name, 0)
            return SSAVariable(var_name, version)
        elif isinstance(expr, ArrayAccess):
            array_name = expr.array.name
            ssa_index = self._transform_expression(expr.index)
            version = self.var_versions.get(array_name, 0)
            return SSAArrayAccess(array_name, ssa_index, version)
        elif isinstance(expr, Literal):
            return SSALiteral(expr.value, expr.type)
        else:
            raise TypeError(f"Unsupported expression type: {type(expr)}")
    
    def _increment_version(self, var_name: str) -> None:
        """Increment the version of a variable."""
        self.var_versions[var_name] = self.var_versions.get(var_name, 0) + 1