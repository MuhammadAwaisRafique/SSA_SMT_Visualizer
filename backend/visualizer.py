"""
Visualizer for the Formal Methods Analyzer.
This module provides visualization utilities for the analysis results.
"""

from typing import Dict, List, Set, Tuple, Optional, Any, Union
import json

from parser import (
    ASTNode, Program, Assignment, IfStatement, WhileLoop, 
    ForLoop, BinaryOp, Variable, ArrayAccess, Literal, AssertStatement
)

from ssa_transformer import (
    SSANode, SSAProgram, SSAAssignment, SSAIfStatement, SSAWhileLoop,
    SSAForLoop, SSABinaryOp, SSAVariable, SSAArrayAccess, SSALiteral,
    SSAAssertStatement, PhiFunction
)

class Visualizer:
    """Provides visualization utilities for program analysis."""
    
    def __init__(self):
        self.node_id = 0
    
    def generate_cfg(self, program: Program) -> Dict:
        """Generate a control flow graph from a program."""
        self.node_id = 0
        nodes = []
        edges = []
        
        # Start node
        start_id = self._get_next_id()
        nodes.append({
            'id': str(start_id),
            'type': 'input',
            'data': {'label': 'Start'},
            'position': {'x': 250, 'y': 0}
        })
        
        # Process program statements
        last_node_id = start_id
        for i, stmt in enumerate(program.statements):
            new_nodes, new_edges, last_id = self._process_statement_for_cfg(stmt, last_node_id, i * 100)
            nodes.extend(new_nodes)
            edges.extend(new_edges)
            last_node_id = last_id
        
        # End node
        end_id = self._get_next_id()
        nodes.append({
            'id': str(end_id),
            'type': 'output',
            'data': {'label': 'End'},
            'position': {'x': 250, 'y': (len(program.statements) + 1) * 100}
        })
        
        # Connect last statement to end
        edges.append({
            'id': f'e{last_node_id}-{end_id}',
            'source': str(last_node_id),
            'target': str(end_id),
            'animated': False
        })
        
        return {
            'nodes': nodes,
            'edges': edges
        }
    
    def _process_statement_for_cfg(self, stmt: ASTNode, parent_id: int, y_offset: int) -> Tuple[List[Dict], List[Dict], int]:
        """Process a statement for CFG generation."""
        nodes = []
        edges = []
        
        if isinstance(stmt, Assignment):
            # Simple assignment
            node_id = self._get_next_id()
            nodes.append({
                'id': str(node_id),
                'type': 'default',
                'data': {'label': self._format_assignment(stmt)},
                'position': {'x': 250, 'y': y_offset + 100}
            })
            edges.append({
                'id': f'e{parent_id}-{node_id}',
                'source': str(parent_id),
                'target': str(node_id),
                'animated': False
            })
            return nodes, edges, node_id
        
        elif isinstance(stmt, IfStatement):
            # If-else statement
            condition_id = self._get_next_id()
            nodes.append({
                'id': str(condition_id),
                'type': 'condition',
                'data': {'label': self._format_expression(stmt.condition)},
                'position': {'x': 250, 'y': y_offset + 100}
            })
            edges.append({
                'id': f'e{parent_id}-{condition_id}',
                'source': str(parent_id),
                'target': str(condition_id),
                'animated': False
            })
            
            # Then branch
            then_id = self._get_next_id()
            nodes.append({
                'id': str(then_id),
                'type': 'group',
                'data': {'label': 'Then'},
                'position': {'x': 150, 'y': y_offset + 200}
            })
            edges.append({
                'id': f'e{condition_id}-{then_id}',
                'source': str(condition_id),
                'target': str(then_id),
                'label': 'True',
                'animated': False
            })
            
            then_last_id = then_id
            for i, then_stmt in enumerate(stmt.then_branch):
                then_nodes, then_edges, then_last_id = self._process_statement_for_cfg(then_stmt, then_last_id, y_offset + 200 + i * 100)
                nodes.extend(then_nodes)
                edges.extend(then_edges)
            
            # Else branch
            else_id = None
            else_last_id = None
            if stmt.else_branch:
                else_id = self._get_next_id()
                nodes.append({
                    'id': str(else_id),
                    'type': 'group',
                    'data': {'label': 'Else'},
                    'position': {'x': 350, 'y': y_offset + 200}
                })
                edges.append({
                    'id': f'e{condition_id}-{else_id}',
                    'source': str(condition_id),
                    'target': str(else_id),
                    'label': 'False',
                    'animated': False
                })
                
                else_last_id = else_id
                for i, else_stmt in enumerate(stmt.else_branch):
                    else_nodes, else_edges, else_last_id = self._process_statement_for_cfg(else_stmt, else_last_id, y_offset + 200 + i * 100)
                    nodes.extend(else_nodes)
                    edges.extend(else_edges)
            
            # Merge point
            merge_id = self._get_next_id()
            nodes.append({
                'id': str(merge_id),
                'type': 'default',
                'data': {'label': 'Merge'},
                'position': {'x': 250, 'y': y_offset + 300 + (len(stmt.then_branch) + len(stmt.else_branch if stmt.else_branch else [])) * 50}
            })
            
            edges.append({
                'id': f'e{then_last_id}-{merge_id}',
                'source': str(then_last_id),
                'target': str(merge_id),
                'animated': False
            })
            
            if else_last_id:
                edges.append({
                    'id': f'e{else_last_id}-{merge_id}',
                    'source': str(else_last_id),
                    'target': str(merge_id),
                    'animated': False
                })
            else:
                # If no else branch, connect condition directly to merge
                edges.append({
                    'id': f'e{condition_id}-{merge_id}-else',
                    'source': str(condition_id),
                    'target': str(merge_id),
                    'label': 'False',
                    'animated': False
                })
            
            return nodes, edges, merge_id
        
        elif isinstance(stmt, WhileLoop):
            # While loop
            condition_id = self._get_next_id()
            nodes.append({
                'id': str(condition_id),
                'type': 'condition',
                'data': {'label': f'while {self._format_expression(stmt.condition)}'},
                'position': {'x': 250, 'y': y_offset + 100}
            })
            edges.append({
                'id': f'e{parent_id}-{condition_id}',
                'source': str(parent_id),
                'target': str(condition_id),
                'animated': False
            })
            
            # Loop body
            body_id = self._get_next_id()
            nodes.append({
                'id': str(body_id),
                'type': 'group',
                'data': {'label': 'Loop Body'},
                'position': {'x': 250, 'y': y_offset + 200}
            })
            edges.append({
                'id': f'e{condition_id}-{body_id}',
                'source': str(condition_id),
                'target': str(body_id),
                'label': 'True',
                'animated': False
            })
            
            last_body_id = body_id
            for i, body_stmt in enumerate(stmt.body):
                body_nodes, body_edges, last_body_id = self._process_statement_for_cfg(body_stmt, last_body_id, y_offset + 200 + i * 100)
                nodes.extend(body_nodes)
                edges.extend(body_edges)
            
            # Loop back to condition
            edges.append({
                'id': f'e{last_body_id}-{condition_id}',
                'source': str(last_body_id),
                'target': str(condition_id),
                'type': 'step',
                'animated': True,
                'style': {'stroke': '#f6ad55'}
            })
            
            # Exit loop
            exit_id = self._get_next_id()
            nodes.append({
                'id': str(exit_id),
                'type': 'default',
                'data': {'label': 'Loop Exit'},
                'position': {'x': 400, 'y': y_offset + 150}
            })
            edges.append({
                'id': f'e{condition_id}-{exit_id}',
                'source': str(condition_id),
                'target': str(exit_id),
                'label': 'False',
                'animated': False
            })
            
            return nodes, edges, exit_id
        
        elif isinstance(stmt, ForLoop):
            # For loop (similar to while but with init and update)
            init_id = self._get_next_id()
            nodes.append({
                'id': str(init_id),
                'type': 'default',
                'data': {'label': f'Init: {self._format_assignment(stmt.init)}'},
                'position': {'x': 250, 'y': y_offset + 100}
            })
            edges.append({
                'id': f'e{parent_id}-{init_id}',
                'source': str(parent_id),
                'target': str(init_id),
                'animated': False
            })
            
            condition_id = self._get_next_id()
            nodes.append({
                'id': str(condition_id),
                'type': 'condition',
                'data': {'label': f'Condition: {self._format_expression(stmt.condition)}'},
                'position': {'x': 250, 'y': y_offset + 200}
            })
            edges.append({
                'id': f'e{init_id}-{condition_id}',
                'source': str(init_id),
                'target': str(condition_id),
                'animated': False
            })
            
            # Loop body
            body_id = self._get_next_id()
            nodes.append({
                'id': str(body_id),
                'type': 'group',
                'data': {'label': 'Loop Body'},
                'position': {'x': 250, 'y': y_offset + 300}
            })
            edges.append({
                'id': f'e{condition_id}-{body_id}',
                'source': str(condition_id),
                'target': str(body_id),
                'label': 'True',
                'animated': False
            })
            
            last_body_id = body_id
            for i, body_stmt in enumerate(stmt.body):
                body_nodes, body_edges, last_body_id = self._process_statement_for_cfg(body_stmt, last_body_id, y_offset + 300 + i * 100)
                nodes.extend(body_nodes)
                edges.extend(body_edges)
            
            # Update
            update_id = self._get_next_id()
            nodes.append({
                'id': str(update_id),
                'type': 'default',
                'data': {'label': f'Update: {self._format_assignment(stmt.update)}'},
                'position': {'x': 150, 'y': y_offset + 250}
            })
            edges.append({
                'id': f'e{last_body_id}-{update_id}',
                'source': str(last_body_id),
                'target': str(update_id),
                'animated': False
            })
            
            # Loop back to condition
            edges.append({
                'id': f'e{update_id}-{condition_id}',
                'source': str(update_id),
                'target': str(condition_id),
                'type': 'step',
                'animated': True,
                'style': {'stroke': '#f6ad55'}
            })
            
            # Exit loop
            exit_id = self._get_next_id()
            nodes.append({
                'id': str(exit_id),
                'type': 'default',
                'data': {'label': 'Loop Exit'},
                'position': {'x': 400, 'y': y_offset + 200}
            })
            edges.append({
                'id': f'e{condition_id}-{exit_id}',
                'source': str(condition_id),
                'target': str(exit_id),
                'label': 'False',
                'animated': False
            })
            
            return nodes, edges, exit_id
        
        elif isinstance(stmt, AssertStatement):
            # Assert statement
            node_id = self._get_next_id()
            nodes.append({
                'id': str(node_id),
                'type': 'assertion',
                'data': {'label': f'assert({self._format_expression(stmt.condition)})'},
                'position': {'x': 250, 'y': y_offset + 100},
                'style': {'borderColor': '#f6ad55', 'borderWidth': 2}
            })
            edges.append({
                'id': f'e{parent_id}-{node_id}',
                'source': str(parent_id),
                'target': str(node_id),
                'animated': False
            })
            return nodes, edges, node_id
        
        # Default case
        node_id = self._get_next_id()
        nodes.append({
            'id': str(node_id),
            'type': 'default',
            'data': {'label': 'Unknown Statement'},
            'position': {'x': 250, 'y': y_offset + 100}
        })
        edges.append({
            'id': f'e{parent_id}-{node_id}',
            'source': str(parent_id),
            'target': str(node_id),
            'animated': False
        })
        return nodes, edges, node_id
    
    def format_ssa(self, ssa_program: SSAProgram) -> str:
        """Format an SSA program for display."""
        lines = []
        for stmt in ssa_program.statements:
            formatted = self._format_ssa_statement(stmt)
            if isinstance(formatted, list):
                lines.extend(formatted)
            else:
                lines.append(formatted)
        return "\n".join(lines)
    
    def _format_ssa_statement(self, stmt: SSANode, indent: int = 0) -> Union[str, List[str]]:
        """Format an SSA statement for display."""
        indent_str = "  " * indent
        
        if isinstance(stmt, SSAAssignment):
            return f"{indent_str}{self._format_ssa_variable(stmt.variable)} := {self._format_ssa_expression(stmt.expression)};"
        
        elif isinstance(stmt, SSAIfStatement):
            lines = [f"{indent_str}if ({self._format_ssa_expression(stmt.condition)}) {{"]
            
            # Then branch
            for s in stmt.then_branch:
                formatted = self._format_ssa_statement(s, indent + 1)
                if isinstance(formatted, list):
                    lines.extend(formatted)
                else:
                    lines.append(formatted)
            
            # Else branch
            if stmt.else_branch:
                lines.append(f"{indent_str}}} else {{")
                for s in stmt.else_branch:
                    formatted = self._format_ssa_statement(s, indent + 1)
                    if isinstance(formatted, list):
                        lines.extend(formatted)
                    else:
                        lines.append(formatted)
            
            lines.append(f"{indent_str}}}")
            
            # Phi functions
            for phi in stmt.phi_functions:
                lines.append(f"{indent_str}{phi};")
            
            return lines
        
        elif isinstance(stmt, SSAWhileLoop):
            lines = [f"{indent_str}while ({self._format_ssa_expression(stmt.condition)}) {{"]
            
            for s in stmt.body:
                formatted = self._format_ssa_statement(s, indent + 1)
                if isinstance(formatted, list):
                    lines.extend(formatted)
                else:
                    lines.append(formatted)
            
            lines.append(f"{indent_str}}}")
            
            # Phi functions
            for phi in stmt.phi_functions:
                lines.append(f"{indent_str}{phi};")
            
            return lines
        
        elif isinstance(stmt, SSAForLoop):
            init_str = self._format_ssa_statement(stmt.init).strip()
            condition_str = self._format_ssa_expression(stmt.condition)
            update_str = self._format_ssa_statement(stmt.update).strip()
            
            lines = [f"{indent_str}for ({init_str} {condition_str}; {update_str[:-1]}) {{"]
            
            for s in stmt.body:
                formatted = self._format_ssa_statement(s, indent + 1)
                if isinstance(formatted, list):
                    lines.extend(formatted)
                else:
                    lines.append(formatted)
            
            lines.append(f"{indent_str}}}")
            
            # Phi functions
            for phi in stmt.phi_functions:
                lines.append(f"{indent_str}{phi};")
            
            return lines
        
        elif isinstance(stmt, SSAAssertStatement):
            return f"{indent_str}assert({self._format_ssa_expression(stmt.condition)});"
        
        return f"{indent_str}// Unknown statement: {type(stmt).__name__}"
    
    def _format_ssa_expression(self, expr: SSANode) -> str:
        """Format an SSA expression for display."""
        if isinstance(expr, SSABinaryOp):
            left = self._format_ssa_expression(expr.left)
            right = self._format_ssa_expression(expr.right)
            return f"({left} {expr.op} {right})"
        
        elif isinstance(expr, SSAVariable):
            return str(expr)
        
        elif isinstance(expr, SSAArrayAccess):
            index = self._format_ssa_expression(expr.index)
            return f"{expr.array}[{index}]_{expr.version}"
        
        elif isinstance(expr, SSALiteral):
            return str(expr.value)
        
        return str(expr)
    
    def _format_ssa_variable(self, var: Union[SSAVariable, SSAArrayAccess]) -> str:
        """Format an SSA variable for display."""
        if isinstance(var, SSAVariable):
            return str(var)
        elif isinstance(var, SSAArrayAccess):
            index = self._format_ssa_expression(var.index)
            return f"{var.array}[{index}]_{var.version}"
        return str(var)
    
    def _format_assignment(self, stmt: Assignment) -> str:
        """Format an assignment statement for display."""
        if isinstance(stmt.variable, Variable):
            var_str = stmt.variable.name
        elif isinstance(stmt.variable, ArrayAccess):
            var_str = f"{stmt.variable.array.name}[{self._format_expression(stmt.variable.index)}]"
        else:
            var_str = str(stmt.variable)
        
        expr_str = self._format_expression(stmt.expression)
        return f"{var_str} := {expr_str}"
    
    def _format_expression(self, expr: ASTNode) -> str:
        """Format an expression for display."""
        if isinstance(expr, BinaryOp):
            left = self._format_expression(expr.left)
            right = self._format_expression(expr.right)
            return f"({left} {expr.op} {right})"
        
        elif isinstance(expr, Variable):
            return expr.name
        
        elif isinstance(expr, ArrayAccess):
            index = self._format_expression(expr.index)
            return f"{expr.array.name}[{index}]"
        
        elif isinstance(expr, Literal):
            return str(expr.value)
        
        return str(expr)
    
    def _get_next_id(self) -> int:
        """Get the next unique node ID."""
        self.node_id += 1
        return self.node_id