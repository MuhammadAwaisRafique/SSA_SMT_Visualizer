"""
Parser for the custom mini-language used in the Formal Methods Analyzer.
This module parses programs written in the mini-language and converts them
to an abstract syntax tree (AST) for further processing.
"""

import re
from typing import Dict, List, Union, Tuple, Optional

class ASTNode:
    """Base class for all AST nodes."""
    pass

class Program(ASTNode):
    """Represents a complete program."""
    def __init__(self, statements):
        self.statements = statements

class Assignment(ASTNode):
    """Represents an assignment statement: x := expr"""
    def __init__(self, variable, expression):
        self.variable = variable
        self.expression = expression

class IfStatement(ASTNode):
    """Represents an if-else statement."""
    def __init__(self, condition, then_branch, else_branch=None):
        self.condition = condition
        self.then_branch = then_branch
        self.else_branch = else_branch

class WhileLoop(ASTNode):
    """Represents a while loop."""
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

class ForLoop(ASTNode):
    """Represents a for loop."""
    def __init__(self, init, condition, update, body):
        self.init = init
        self.condition = condition
        self.update = update
        self.body = body

class BinaryOp(ASTNode):
    """Represents a binary operation."""
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

class Variable(ASTNode):
    """Represents a variable reference."""
    def __init__(self, name):
        self.name = name

class ArrayAccess(ASTNode):
    """Represents array access: arr[index]"""
    def __init__(self, array, index):
        self.array = array
        self.index = index

class Literal(ASTNode):
    """Represents a literal value (number, boolean, etc.)"""
    def __init__(self, value, type_name):
        self.value = value
        self.type = type_name

class AssertStatement(ASTNode):
    """Represents an assertion: assert(condition)"""
    def __init__(self, condition):
        self.condition = condition

class Parser:
    """Parser for the custom mini-language."""
    
    def __init__(self):
        self.tokens = []
        self.current_pos = 0
    
    def parse(self, code: str) -> Program:
        """Parse the given code and return the AST."""
        self.tokenize(code)
        self.current_pos = 0
        statements = self.parse_statements()
        return Program(statements)
    
    def tokenize(self, code: str) -> None:
        """Convert code string into tokens."""
        # Remove comments
        code = re.sub(r'//.*', '', code)
        
        # Define token patterns
        token_patterns = [
            ('SEMICOLON', r';'),
            ('ASSIGN', r':='),
            ('LPAREN', r'\('),
            ('RPAREN', r'\)'),
            ('LBRACE', r'\{'),
            ('RBRACE', r'\}'),
            ('LBRACKET', r'\['),
            ('RBRACKET', r'\]'),
            ('COMMA', r','),
            ('OP', r'[+\-*/]'),
            ('COMP', r'==|!=|<=|>=|<|>'),
            ('IF', r'if'),
            ('ELSE', r'else'),
            ('WHILE', r'while'),
            ('FOR', r'for'),
            ('ASSERT', r'assert'),
            ('IN', r'in'),
            ('RANGE', r'range'),
            ('NUMBER', r'\d+'),
            ('IDENTIFIER', r'[a-zA-Z_][a-zA-Z0-9_]*'),
            ('WHITESPACE', r'\s+'),
        ]
        
        # Create regex pattern
        patterns = '|'.join(f'(?P<{name}>{pattern})' for name, pattern in token_patterns)
        regex = re.compile(patterns)
        
        # Tokenize
        self.tokens = []
        for match in regex.finditer(code):
            token_type = match.lastgroup
            token_value = match.group()
            
            if token_type != 'WHITESPACE':  # Skip whitespace
                self.tokens.append((token_type, token_value))
    
    def match(self, token_type: str) -> bool:
        """Check if the current token matches the expected type."""
        if self.current_pos < len(self.tokens):
            current_type, _ = self.tokens[self.current_pos]
            return current_type == token_type
        return False
    
    def consume(self, token_type: str) -> str:
        """Consume the current token if it matches the expected type."""
        if self.match(token_type):
            _, value = self.tokens[self.current_pos]
            self.current_pos += 1
            return value
        raise SyntaxError(f"Expected {token_type}, got {self.tokens[self.current_pos] if self.current_pos < len(self.tokens) else 'EOF'}")
    
    def peek(self) -> Tuple[str, str]:
        """Return the current token without consuming it."""
        if self.current_pos < len(self.tokens):
            return self.tokens[self.current_pos]
        return ('EOF', '')
    
    def parse_statements(self) -> List[ASTNode]:
        """Parse a sequence of statements."""
        statements = []
        
        while self.current_pos < len(self.tokens) and not self.match('RBRACE'):
            statement = self.parse_statement()
            statements.append(statement)
        
        return statements
    
    def parse_statement(self) -> ASTNode:
        """Parse a single statement."""
        if self.match('IF'):
            return self.parse_if_statement()
        elif self.match('WHILE'):
            return self.parse_while_loop()
        elif self.match('FOR'):
            return self.parse_for_loop()
        elif self.match('ASSERT'):
            return self.parse_assert()
        elif self.match('IDENTIFIER'):
            return self.parse_assignment()
        else:
            raise SyntaxError(f"Unexpected token: {self.peek()}")
    
    def parse_if_statement(self) -> IfStatement:
        """Parse an if statement."""
        self.consume('IF')
        self.consume('LPAREN')
        condition = self.parse_expression()
        self.consume('RPAREN')
        self.consume('LBRACE')
        then_branch = self.parse_statements()
        self.consume('RBRACE')
        
        else_branch = None
        if self.match('ELSE'):
            self.consume('ELSE')
            self.consume('LBRACE')
            else_branch = self.parse_statements()
            self.consume('RBRACE')
        
        return IfStatement(condition, then_branch, else_branch)
    
    def parse_while_loop(self) -> WhileLoop:
        """Parse a while loop."""
        self.consume('WHILE')
        self.consume('LPAREN')
        condition = self.parse_expression()
        self.consume('RPAREN')
        self.consume('LBRACE')
        body = self.parse_statements()
        self.consume('RBRACE')
        
        return WhileLoop(condition, body)
    
    def parse_for_loop(self) -> ForLoop:
        """Parse a for loop."""
        self.consume('FOR')
        self.consume('LPAREN')
        
        # Parse initialization
        init = self.parse_assignment()
        
        # Parse condition
        condition = self.parse_expression()
        self.consume('SEMICOLON')
        
        # Parse update
        update = self.parse_assignment(semicolon=False)
        
        self.consume('RPAREN')
        self.consume('LBRACE')
        body = self.parse_statements()
        self.consume('RBRACE')
        
        return ForLoop(init, condition, update, body)
    
    def parse_assignment(self, semicolon=True) -> Assignment:
        """Parse an assignment statement."""
        var_name = self.consume('IDENTIFIER')
        
        # Check if this is an array access
        variable = None
        if self.match('LBRACKET'):
            self.consume('LBRACKET')
            index = self.parse_expression()
            self.consume('RBRACKET')
            variable = ArrayAccess(Variable(var_name), index)
        else:
            variable = Variable(var_name)
        
        self.consume('ASSIGN')
        expression = self.parse_expression()
        
        if semicolon:
            self.consume('SEMICOLON')
        
        return Assignment(variable, expression)
    
    def parse_assert(self) -> AssertStatement:
        """Parse an assert statement."""
        self.consume('ASSERT')
        self.consume('LPAREN')
        condition = self.parse_expression()
        self.consume('RPAREN')
        self.consume('SEMICOLON')
        
        return AssertStatement(condition)
    
    def parse_expression(self) -> ASTNode:
        """Parse an expression."""
        return self.parse_comparison()
    
    def parse_comparison(self) -> ASTNode:
        """Parse a comparison expression."""
        left = self.parse_addition()
        
        if self.match('COMP'):
            op = self.consume('COMP')
            right = self.parse_addition()
            return BinaryOp(op, left, right)
        
        return left
    
    def parse_addition(self) -> ASTNode:
        """Parse an addition/subtraction expression."""
        left = self.parse_term()
        
        while self.match('OP') and self.peek()[1] in ['+', '-']:
            op = self.consume('OP')
            right = self.parse_term()
            left = BinaryOp(op, left, right)
        
        return left
    
    def parse_term(self) -> ASTNode:
        """Parse a multiplication/division expression."""
        left = self.parse_factor()
        
        while self.match('OP') and self.peek()[1] in ['*', '/']:
            op = self.consume('OP')
            right = self.parse_factor()
            left = BinaryOp(op, left, right)
        
        return left
    
    def parse_factor(self) -> ASTNode:
        """Parse a factor (literal, variable, or parenthesized expression)."""
        if self.match('NUMBER'):
            value = int(self.consume('NUMBER'))
            return Literal(value, 'int')
        elif self.match('IDENTIFIER'):
            var_name = self.consume('IDENTIFIER')
            
            # Check if this is an array access
            if self.match('LBRACKET'):
                self.consume('LBRACKET')
                index = self.parse_expression()
                self.consume('RBRACKET')
                return ArrayAccess(Variable(var_name), index)
            
            return Variable(var_name)
        elif self.match('LPAREN'):
            self.consume('LPAREN')
            expr = self.parse_expression()
            self.consume('RPAREN')
            return expr
        else:
            raise SyntaxError(f"Unexpected token in factor: {self.peek()}")