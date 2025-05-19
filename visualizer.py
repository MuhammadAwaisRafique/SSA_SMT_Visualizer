import matplotlib.pyplot as plt
import networkx as nx
from typing import Dict, List, Set, Tuple, Any, Optional
from parser import *
from ssa import *

def generate_cfg(ast_or_ssa) -> plt.Figure:
    """
    Generate a Control Flow Graph (CFG) for the given AST or SSA program.
    
    Args:
        ast_or_ssa: The AST or SSA program to visualize
        
    Returns:
        A matplotlib Figure containing the CFG
    """
    # Create a directed graph
    G = nx.DiGraph()
    
    # Counter for node IDs
    node_counter = 0
    
    # Helper function to generate a new node ID
    def get_new_node_id():
        nonlocal node_counter
        node_id = f"node_{node_counter}"
        node_counter += 1
        return node_id
    
    # Helper function to create a node label for an AST node
    def create_node_label(node):
        if isinstance(node, VarDecl) or isinstance(node, SSAVarDecl):
            return f"var {node.name} = ..."
        elif isinstance(node, Assignment) or isinstance(node, SSAAssignment):
            return f"{node.name} = ..."
        elif isinstance(node, While) or isinstance(node, SSAWhile):
            return "while (...)"
        elif isinstance(node, If) or isinstance(node, SSAIf):
            return "if (...)"
        elif isinstance(node, Assert) or isinstance(node, SSAAssert):
            return "assert (...)"
        elif isinstance(node, Program) or isinstance(node, SSAProgram):
            return "Program"
        elif isinstance(node, list):
            return "Block"
        else:
            return str(type(node).__name__)
    
    # Helper function to build the CFG from an AST
    def build_cfg_from_ast(node, parent_id=None):
        if node is None:
            return None
        
        # Create a node for this AST node
        node_id = get_new_node_id()
        G.add_node(node_id, label=create_node_label(node))
        
        # Connect to parent if provided
        if parent_id is not None:
            G.add_edge(parent_id, node_id)
        
        # Process based on node type
        if isinstance(node, Program):
            last_id = node_id
            for stmt in node.statements:
                last_id = build_cfg_from_ast(stmt, last_id)
            return last_id
        
        elif isinstance(node, SSAProgram):
            last_id = node_id
            for stmt in node.statements:
                last_id = build_cfg_from_ast(stmt, last_id)
            return last_id
        
        elif isinstance(node, VarDecl) or isinstance(node, Assignment) or \
             isinstance(node, Assert) or isinstance(node, SSAVarDecl) or \
             isinstance(node, SSAAssignment) or isinstance(node, SSAAssert) or \
             isinstance(node, SSAPhiFunction):
            return node_id
        
        elif isinstance(node, While) or isinstance(node, SSAWhile):
            # Create a condition node
            cond_id = get_new_node_id()
            G.add_node(cond_id, label="condition")
            G.add_edge(node_id, cond_id)
            
            # Process the body
            if isinstance(node, While):
                body_nodes = node.body
            else:  # SSAWhile
                body_nodes = node.body
            
            last_body_id = cond_id
            for stmt in body_nodes:
                last_body_id = build_cfg_from_ast(stmt, last_body_id)
            
            # Loop back to condition
            G.add_edge(last_body_id, cond_id)
            
            # Edge for exiting the loop
            exit_id = get_new_node_id()
            G.add_node(exit_id, label="exit loop")
            G.add_edge(cond_id, exit_id)
            
            return exit_id
        
        elif isinstance(node, If) or isinstance(node, SSAIf):
            # Create a condition node
            cond_id = get_new_node_id()
            G.add_node(cond_id, label="condition")
            G.add_edge(node_id, cond_id)
            
            # Process the true branch
            if isinstance(node, If):
                true_branch = node.true_branch
                false_branch = node.false_branch
            else:  # SSAIf
                true_branch = node.true_branch
                false_branch = node.false_branch
            
            true_id = get_new_node_id()
            G.add_node(true_id, label="true branch")
            G.add_edge(cond_id, true_id)
            
            last_true_id = true_id
            for stmt in true_branch:
                last_true_id = build_cfg_from_ast(stmt, last_true_id)
            
            # Process the false branch if it exists
            if false_branch:
                false_id = get_new_node_id()
                G.add_node(false_id, label="false branch")
                G.add_edge(cond_id, false_id)
                
                last_false_id = false_id
                for stmt in false_branch:
                    last_false_id = build_cfg_from_ast(stmt, last_false_id)
                
                # Create a merge node
                merge_id = get_new_node_id()
                G.add_node(merge_id, label="merge")
                G.add_edge(last_true_id, merge_id)
                G.add_edge(last_false_id, merge_id)
                
                return merge_id
            else:
                # No false branch, just return the end of the true branch
                return last_true_id
        
        elif isinstance(node, list):
            # Process a list of statements
            last_id = node_id
            for stmt in node:
                last_id = build_cfg_from_ast(stmt, last_id)
            return last_id
        
        else:
            # Default case
            return node_id
    
    # Build the CFG
    build_cfg_from_ast(ast_or_ssa)
    
    # Create a Figure
    fig = plt.figure(figsize=(10, 8))
    
    # Draw the graph
    pos = nx.spring_layout(G, seed=42)  # Consistent layout
    node_labels = {node: data['label'] for node, data in G.nodes(data=True)}
    
    nx.draw(G, pos, with_labels=False, node_color='lightblue', 
            node_size=500, arrowsize=20, font_size=10,
            edge_color='gray', arrows=True)
    
    nx.draw_networkx_labels(G, pos, labels=node_labels, font_size=8)
    
    plt.axis('off')
    plt.tight_layout()
    
    return fig
