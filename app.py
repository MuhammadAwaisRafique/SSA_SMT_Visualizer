import streamlit as st
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from parser import parse_program
from ssa import convert_to_ssa, unroll_loops
from smt import generate_smt, check_assertion, check_equivalence
from optimizer import optimize_ssa
from visualizer import generate_cfg
from example_programs import *

# Page configuration
st.set_page_config(
    page_title="Code Verifier Tool",
    page_icon="🔍",
    layout="wide",
)

# Custom CSS for a beautiful, readable, and cohesive UI
st.markdown("""
<style>
    /* Root variables for consistent theming */
    :root {
        --primary-color: #8B5CF6;
        --secondary-color: #22D3EE;
        --accent-color: #F472B6;
        --background-color: #0F172A;
        --card-background: #1E293B;
        --text-color: #E2E8F0;
        --success-color: #10B981;
        --error-color: #EF4444;
        --warning-color: #FBBF24;
        --code-background: #1E293B;
        --code-text-color: #D1D5DB;
        --border-color: #334155;
    }

    /* Global reset and font */
    * {
        font-family: 'Poppins', sans-serif;
        box-sizing: border-box;
        margin: 0;
        padding: 0;
    }

    /* Main app background */
    .stApp, .main {
        background: linear-gradient(135deg, var(--background-color) 0%, #1E293B 100%) !important;
        color: var(--text-color);
        padding: 2rem;
        min-height: 100vh;
    }

    /* Sidebar styling */
    [data-testid="stSidebar"] {
        background: var(--background-color) !important;
        border-right: 1px solid var(--border-color);
        padding: 1.5rem;
    }

    /* Sidebar header */
    [data-testid="stSidebar"] h2 {
        background: linear-gradient(90deg, var(--primary-color), var(--accent-color)) !important;
        -webkit-background-clip: text !important;
        -webkit-text-fill-color: transparent !important;
        color: var(--primary-color); /* Fallback */
        font-size: 1.5rem;
        margin-bottom: 1.5rem;
        padding: 0.5rem 1rem;
        border-radius: 8px;
        background-color: var(--card-background);
    }

    /* Headings */
    h1, h2, h3 {
        font-family: 'Poppins', sans-serif;
        font-weight: 600;
        background: linear-gradient(90deg, var(--primary-color), var(--accent-color)) !important;
        -webkit-background-clip: text !important;
        -webkit-text-fill-color: transparent !important;
        color: var(--primary-color); /* Fallback */
        letter-spacing: -0.02em;
        padding: 0.5rem 1rem;
        border-radius: 8px;
        background-color: var(--card-background);
    }

    h1 {
        font-size: 2.75rem;
        margin-bottom: 1.5rem;
    }

    h2 {
        font-size: 1.5rem;
    }

    h3 {
        font-size: 1.25rem;
    }

    /* Sidebar elements */
    [data-testid="stSidebar"] label, [data-testid="stSidebar"] .stRadio label, [data-testid="stSidebar"] .stSlider label {
        color: var(--text-color) !important;
        font-weight: 500;
    }

    /* Slider customization */
    .stSlider [data-baseweb="slider"] {
        background: var(--card-background) !important;
    }
    .stSlider [data-baseweb="thumb"] {
        background: var(--secondary-color) !important;
        border: 2px solid var(--card-background) !important;
    }
    .stSlider [data-baseweb="track"] {
        background: var(--border-color) !important;
    }

    /* Card-based UI components */
    .stExpander, .stTextArea, .stSelectbox, .stSlider, .stMultiSelect, .stRadio, [data-testid="stForm"] {
        background: var(--card-background) !important;
        border: 1px solid var(--border-color);
        border-radius: 12px;
        padding: 1.5rem;
        box-shadow: 0 6px 24px rgba(0, 0, 0, 0.3);
        transition: transform 0.3s ease, box-shadow 0.3s ease;
    }

    .stExpander:hover, .stTextArea:hover, .stSelectbox:hover, .stSlider:hover, .stMultiSelect:hover, .stRadio:hover {
        transform: translateY(-4px);
        box-shadow: 0 10px 32px rgba(139, 92, 246, 0.2);
    }

    /* Text area for code input */
    textarea {
        background: var(--code-background) !important;
        color: var(--code-text-color) !important;
        font-family: 'Fira Code', monospace !important;
        font-size: 0.95rem;
        border: 1px solid var(--border-color) !important;
        border-radius: 8px;
        padding: 0.75rem;
    }

    /* Select boxes and inputs */
    select, .stSelectbox > div > div {
        background: var(--code-background) !important;
        color: var(--code-text-color) !important;
        border: 1px solid var(--border-color) !important;
        border-radius: 8px;
    }

    /* Buttons */
    .stButton > button {
        background: linear-gradient(90deg, var(--primary-color), var(--accent-color)) !important;
        color: white !important;
        border: none !important;
        border-radius: 10px;
        padding: 0.75rem 2rem;
        font-family: 'Poppins', sans-serif;
        font-weight: 500;
        font-size: 1rem;
        transition: all 0.3s ease;
    }

    .stButton > button:hover {
        background: var(--secondary-color) !important;
        transform: scale(1.05);
        box-shadow: 0 4px 16px rgba(34, 211, 238, 0.4);
    }

    /* Code blocks */
    .stCodeBlock, pre {
        background: var(--code-background) !important;
        border: 1px solid var(--border-color);
        border-radius: 10px;
        padding: 1.25rem;
        font-family: 'Fira Code', monospace !important;
        font-size: 0.9rem;
        color: var(--code-text-color);
        box-shadow: inset 0 2px 8px rgba(0, 0, 0, 0.2);
    }

    /* Tables */
    [data-testid="stTable"] {
        background: var(--card-background);
        border: 1px solid var(--border-color);
        border-radius: 10px;
        padding: 1.25rem;
        color: var(--text-color);
    }

    /* Tabs */
    .stTabs [data-baseweb="tab"] {
        font-family: 'Poppins', sans-serif;
        color: var(--text-color);
        font-weight: 500;
        padding: 0.75rem 1.5rem;
        border-radius: 8px;
        background: var(--card-background);
        margin-right: 0.5rem;
        transition: all 0.3s ease;
    }

    .stTabs [data-baseweb="tab"]:hover, .stTabs [data-baseweb="tab-highlight"] {
        background: var(--primary-color) !important;
        color: white !important;
    }

    /* Slider and radio buttons */
    .stSlider [data-baseweb="slider"] {
        background: var(--card-background) !important;
    }

    .stRadio > label, .stMultiSelect > label, .stSlider > label, .stSelectbox > label {
        color: var(--text-color);
        font-family: 'Poppins', sans-serif;
        font-weight: 500;
    }

    /* Success, error, and warning messages */
    .stSuccess {
        background: var(--success-color) !important;
        color: #111827 !important;
        border-radius: 10px;
        padding: 1rem;
        font-family: 'Poppins', sans-serif;
    }

    .stError {
        background: var(--error-color) !important;
        color: white !important;
        border-radius: 10px;
        padding: 1rem;
        font-family: 'Poppins', sans-serif;
    }

    .stWarning {
        background: var(--warning-color) !important;
        color: #111827 !important;
        border-radius: 10px;
        padding: 1rem;
        font-family: 'Poppins', sans-serif;
    }

    /* Markdown and general text */
    .stMarkdown, p, label {
        color: var(--text-color) !important;
        font-family: 'Poppins', sans-serif;
        font-size: 1rem;
    }

    /* Footer */
    footer, .stMarkdown > div > p {
        text-align: center;
        color: var(--text-color);
        opacity: 0.8;
        margin-top: 2rem;
        font-family: 'Poppins', sans-serif;
        font-size: 0.95rem;
    }
</style>
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700&family=Fira+Code:wght@400;500&display=swap" rel="stylesheet">
""", unsafe_allow_html=True)

# Main title
st.title("Code Verifier & Equivalence Checker")

# Sidebar for mode selection and configuration
with st.sidebar:
    st.header("⚙️ Settings")
    mode = st.radio("Mode", ["Verification", "Equivalence"], help="Choose between verifying assertions or checking code equivalence")
    unroll_depth = st.slider("Loop Unrolling Depth", 1, 10, 3, help="Set the depth for loop unrolling")
    optimization = st.multiselect(
        "SSA Optimizations",
        ["Constant Propagation", "Dead Code Elimination", "Common Subexpression Elimination"],
        default=["Constant Propagation"],
        help="Select optimizations to apply to SSA form"
    )

# Custom language example
example_verification = """
// Example for verification mode
// This program checks if a variable ends up as expected

var x := 10;
var y := 5;
var z := 0;

while (y > 0) {
    z := z + x;
    y := y - 1;
}

assert z == 50; // This should verify as true
"""

example_equivalence_1 = """
// Example for equivalence - Program 1
// Compute sum of 1 to n using a loop

var n := 5;
var sum := 0;
var i := 1;

while (i <= n) {
    sum := sum + i;
    i := i + 1;
}
"""

example_equivalence_2 = """
// Example for equivalence - Program 2
// Compute sum of 1 to n using formula

var n := 5;
var sum := n * (n + 1) / 2;
"""

# Mode-specific UI
if mode == "Verification":
    st.header("🔍 Code Verification")
    st.markdown("""
    Check if your code's assertions are valid for all possible executions. Enter your code with `assert` statements to verify them.
    """)

    # Example selection dropdown
    verification_examples = {
        "Basic While Loop": example_verification,
        "If-Else Statement": IF_ELSE_EXAMPLE,
        "While Loop Counter": WHILE_LOOP_EXAMPLE,
        "Simplified Bubble Sort": BUBBLE_SORT_EXAMPLE,
        "Power Calculation": POWER_CALCULATION,
        "Fibonacci Calculation": FIBONACCI_CALCULATION
    }

    selected_example = st.selectbox(
        "Select an example or write your own:",
        list(verification_examples.keys()),
        help="Choose a pre-built code example or create your own"
    )

    program_text = st.text_area(
        "Program Code",
        value=verification_examples[selected_example],
        height=300,
        help="Enter your code here"
    )

    if st.button("Verify Code"):
        if program_text:
            try:
                # Parse the program
                ast = parse_program(program_text)

                # Display original program
                with st.expander("Original Code", expanded=True):
                    st.code(program_text, language="javascript")

                # Convert to SSA form
                ssa_result = convert_to_ssa(ast)

                # Unroll loops
                unrolled_ssa = unroll_loops(ssa_result, unroll_depth)

                # Display SSA form
                with st.expander("SSA Form", expanded=True):
                    st.code(unrolled_ssa.to_string(), language="javascript")

                # Optimize SSA if requested
                if optimization:
                    optimized_ssa = optimize_ssa(unrolled_ssa, optimization)
                    with st.expander("Optimized SSA Form"):
                        st.code(optimized_ssa.to_string(), language="javascript")
                else:
                    optimized_ssa = unrolled_ssa

                # Generate SMT constraints
                smt_constraints = generate_smt(optimized_ssa)

                # Display SMT constraints
                with st.expander("SMT Constraints", expanded=True):
                    st.code(smt_constraints, language="python")

                # Check assertions
                result, examples, counterexamples = check_assertion(optimized_ssa)

                # Display results
                st.subheader("Verification Results")
                if result:
                    st.success("✅ All assertions hold!")
                    st.subheader("Example Execution")
                    if examples and len(examples) > 0:
                        example_data = list(examples[0].items())
                        example_df = pd.DataFrame(example_data)
                        if not example_df.empty:
                            example_df.columns = ["Variable", "Value"]
                            st.table(example_df)
                        else:
                            st.info("No example data available.")
                    else:
                        st.info("No examples available.")
                else:
                    st.error("❌ Some assertions do not hold!")
                    st.subheader("Counterexamples")
                    if counterexamples and len(counterexamples) > 0:
                        for i, counterexample in enumerate(counterexamples[:2]):
                            st.write(f"Counterexample {i+1}:")
                            counter_data = list(counterexample.items())
                            counter_df = pd.DataFrame(counter_data)
                            if not counter_df.empty:
                                counter_df.columns = ["Variable", "Value"]
                                st.table(counter_df)
                            else:
                                st.info("No counterexample data available.")
                    else:
                        st.info("No counterexamples available.")

                # Generate and display CFG
                st.subheader("Control Flow Graph")
                original_cfg = generate_cfg(ast)
                ssa_cfg = generate_cfg(optimized_ssa)

                col1, col2 = st.columns(2)
                with col1:
                    st.write("Original Code CFG")
                    st.pyplot(original_cfg)

                with col2:
                    st.write("SSA Form CFG")
                    st.pyplot(ssa_cfg)

            except Exception as e:
                st.error(f"An error occurred: {str(e)}")
        else:
            st.warning("Please enter code to verify.")

else:  # Equivalence mode
    st.header("⚖️ Code Equivalence")
    st.markdown("""
    Compare two pieces of code to see if they produce the same results for all inputs.
    """)

    # Example pairs for equivalence checking
    equivalence_examples = {
        "Sum Calculation": {
            "Program 1": SUM_LOOP,
            "Program 2": SUM_FORMULA
        },
        "Factorial Calculation": {
            "Program 1": FACTORIAL_LOOP,
            "Program 2": FACTORIAL_RECURSIVE
        }
    }

    selected_example_pair = st.selectbox(
        "Select an example pair or create your own:",
        list(equivalence_examples.keys()),
        help="Choose a pre-built pair or write your own code"
    )

    col1, col2 = st.columns(2)

    with col1:
        st.subheader("Code 1")
        program1_text = st.text_area(
            "First Code",
            value=equivalence_examples[selected_example_pair]["Program 1"],
            height=250,
            help="Enter the first code here"
        )

    with col2:
        st.subheader("Code 2")
        program2_text = st.text_area(
            "Second Code",
            value=equivalence_examples[selected_example_pair]["Program 2"],
            height=250,
            help="Enter the second code here"
        )

    if st.button("Check Equivalence"):
        if program1_text and program2_text:
            try:
                # Parse programs
                ast1 = parse_program(program1_text)
                ast2 = parse_program(program2_text)

                # Convert to SSA forms
                ssa_result1 = convert_to_ssa(ast1)
                ssa_result2 = convert_to_ssa(ast2)

                # Unroll loops
                unrolled_ssa1 = unroll_loops(ssa_result1, unroll_depth)
                unrolled_ssa2 = unroll_loops(ssa_result2, unroll_depth)

                # Display SSA forms
                col1, col2 = st.columns(2)
                with col1:
                    st.subheader("Code 1 - SSA Form")
                    st.code(unrolled_ssa1.to_string(), language="javascript")

                with col2:
                    st.subheader("Code 2 - SSA Form")
                    st.code(unrolled_ssa2.to_string(), language="javascript")

                # Optimize if requested
                if optimization:
                    optimized_ssa1 = optimize_ssa(unrolled_ssa1, optimization)
                    optimized_ssa2 = optimize_ssa(unrolled_ssa2, optimization)

                    col1, col2 = st.columns(2)
                    with col1:
                        st.subheader("Code 1 - Optimized SSA")
                        st.code(optimized_ssa1.to_string(), language="javascript")

                    with col2:
                        st.subheader("Code 2 - Optimized SSA")
                        st.code(optimized_ssa2.to_string(), language="javascript")
                else:
                    optimized_ssa1 = unrolled_ssa1
                    optimized_ssa2 = unrolled_ssa2

                # Generate SMT constraints for equivalence checking
                smt_constraints = generate_smt(optimized_ssa1, optimized_ssa2)

                # Display SMT constraints
                with st.expander("SMT Constraints for Equivalence", expanded=True):
                    st.code(smt_constraints, language="python")

                # Check equivalence
                result, examples, counterexamples = check_equivalence(optimized_ssa1, optimized_ssa2)

                # Display results
                st.subheader("Equivalence Results")
                if result:
                    st.success("✅ The code snippets are equivalent!")
                    st.subheader("Example Execution")
                    if examples and len(examples) > 0:
                        variables = list(examples[0].keys())
                        if variables:
                            data = {
                                "Variable": variables,
                                "Code 1 Value": [examples[0][var] for var in variables],
                                "Code 2 Value": [examples[0][var] for var in variables]
                            }
                            example_df = pd.DataFrame(data)
                            st.table(example_df)
                        else:
                            st.info("No example data available.")
                    else:
                        st.info("No examples available.")
                else:
                    st.error("❌ The code snippets are not equivalent!")
                    st.subheader("Counterexamples")
                    if counterexamples and len(counterexamples) > 0:
                        for i, counterexample in enumerate(counterexamples[:2]):
                            st.write(f"Counterexample {i+1}:")
                            variables = list(counterexample.keys())
                            if variables:
                                data = {
                                    "Variable": variables,
                                    "Code 1 Value": [counterexample[var][0] for var in variables],
                                    "Code 2 Value": [counterexample[var][1] for var in variables]
                                }
                                counter_df = pd.DataFrame(data)
                                st.table(counter_df)
                            else:
                                st.info("No counterexample data available.")
                    else:
                        st.info("No counterexamples available.")

                # Generate and display CFGs
                st.subheader("Control Flow Graphs")
                p1_cfg = generate_cfg(ast1)
                p2_cfg = generate_cfg(ast2)
                p1_ssa_cfg = generate_cfg(optimized_ssa1)
                p2_ssa_cfg = generate_cfg(optimized_ssa2)

                tab1, tab2 = st.tabs(["Original Code CFGs", "SSA Form CFGs"])

                with tab1:
                    col1, col2 = st.columns(2)
                    with col1:
                        st.write("Code 1 CFG")
                        st.pyplot(p1_cfg)

                    with col2:
                        st.write("Code 2 CFG")
                        st.pyplot(p2_cfg)

                with tab2:
                    col1, col2 = st.columns(2)
                    with col1:
                        st.write("Code 1 SSA CFG")
                        st.pyplot(p1_ssa_cfg)

                    with col2:
                        st.write("Code 2 SSA CFG")
                        st.pyplot(p2_ssa_cfg)

            except Exception as e:
                st.error(f"An error occurred: {str(e)}")
        else:
            st.warning("Please enter both code snippets to check equivalence.")

# Footer
st.markdown("---")
st.markdown("🔍 Code Verifier - Built with Streamlit, Z3, and formal methods", unsafe_allow_html=True)