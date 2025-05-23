# Code Verifier and Equivalence Checker Tool

Live App: [https://ssa-smt-visuallizer-by-awais.streamlit.app/](https://ssa-smt-visuallizer-by-awais.streamlit.app/)

## 📌 Objective

This project is a graphical tool built to analyze the **correctness** and **equivalence** of programs using formal verification techniques. Key features include:

- ✅ Parse custom mini-language programs.
- ✅ Transform to Static Single Assignment (SSA) form.
- ✅ Generate SMT constraints.
- ✅ Use Z3 SMT solver for correctness and equivalence checks.
- ✅ Display AST, SSA, SMT code, and CFGs.
- ✅ Support SSA optimizations (DCE, CSE, Constant Propagation).
- ✅ Allow loop unrolling.
- ✅ Graphical Interface with intermediate visualizations.

---

## 🧠 Tool Overview

Built using **Streamlit**, the tool supports two main modes:

- **Verification Mode**: Ensures all assertions hold in a single program.
- **Equivalence Mode**: Compares two programs for semantic equivalence.

The flow:
1. Parse program(s) into AST.
2. Convert to SSA.
3. Apply SSA optimizations.
4. Perform loop unrolling.
5. Generate SMT constraints.
6. Use Z3 to verify or compare.
7. Show all intermediate steps (AST, SSA, SMT, CFGs, Results) in a GUI.

---

## 💻 Language Syntax

The custom mini-language resembles a simplified C/JavaScript. It supports:

### ✔️ Statements

- Variable declarations: `var x := 5;` or `var x = 5;`
- Assignments: `x = 5;`
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparisons: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Logical: `and`, `or`, `not`
- Assertions: `assert x == 5;`
- Comments: `// this is a comment`

### ✔️ Control Flow

- `while (condition) { ... }`
- `for (init; condition; update) { ... }`
- `if (condition) { ... } else { ... }`

### 🚫 Not Supported

- Arrays, functions, procedures, or floating-point precision SMT modeling.

---

## 🧱 Parser Implementation

Implemented in `parser.py` using **PLY (Python Lex-Yacc)**:

- Lexer defines tokens for all language elements.
- Parser builds an **AST** using classes like `Program`, `Assignment`, `If`, `While`, etc.
- Handles errors with token-specific messages.
- AST is the foundation for SSA and SMT generation.

---

## 🔁 SSA Translation

Handled in `ssa.py`. Each variable is versioned (e.g., `x_1`, `x_2`) so that it's assigned once.

### SSA Node Types

- `SSAProgram`, `SSAAssignment`, `SSAVarDecl`
- `SSABinaryOp`, `SSAUnaryOp`, `SSAAssert`
- `SSAWhile`, `SSAIf`, `SSAPhiFunction`

### SSA Transformation Logic

- Tracks variable versions.
- Recursively rewrites AST into SSA form.
- Introduces **phi functions** at control-flow joins (e.g., `x_3 := φ(x_1, x_2)`).

---

## 🔁 Loop Unrolling

Implemented via `unroll_loops()`:

- User specifies depth (default 3, max 10).
- Rewrites `SSAWhile` into repeated `SSAIf` blocks.
- Ensures SSA consistency and termination with added assertions after max depth.

---

## 🧮 SMT Formulation

Defined in `smt.py`, using **Z3** for checking assertions and equivalence.

### ✔️ Verification Mode

- Variables declared as `z3.Int()`.
- Assignments become equality constraints.
- Phi functions become disjunctions.
- Assertions translated to boolean Z3 conditions.

### ✔️ Equivalence Mode

- Inputs shared between two programs.
- Output variable(s) compared.
- Z3 checks whether output of both versions match across all executions.

### Results

- Counterexamples shown if assertion fails or programs differ.
- Displays model values for satisfying input when available.

---

## 🧩 SSA Optimizations

Supported optimizations:

- **Constant Propagation**
- **Dead Code Elimination (DCE)**
- **Common Subexpression Elimination (CSE)**

Applied after SSA conversion and before loop unrolling or SMT generation.

---

## 📈 Control Flow Visualization

- Generates **CFGs (Control Flow Graphs)** for:
  - Original program
  - SSA form
- Displayed using `graphviz` integration in Streamlit.

---

## 🎯 Limitations

- No support for arrays, strings, or floating-point arithmetic in SMT.
- Only basic imperative constructs supported.
- Assertions involving data structures or nested functions are not allowed.

---

## 💡 Potential Improvements

- Add array support.
- Model floating point semantics more accurately.
- Add function/procedure support.
- Advanced optimizations (e.g., Loop Invariant Code Motion).
- Error trace visualization from SMT counterexamples.
- Exporting SMT code and graphs for external use.

---

## 🛠️ Technologies Used

- Python
- Streamlit
- Z3 SMT Solver
- PLY (Lex & Yacc)
- Graphviz (for CFGs)
- Object-oriented SSA AST design

---

## 🔗 Live Demo

👉 Check it out live here:  
[https://ssa-smt-visuallizer-by-awais.streamlit.app/](https://ssa-smt-visuallizer-by-awais.streamlit.app/)
