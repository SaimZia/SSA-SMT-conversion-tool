import gast
from ssa_converter_gast import SSAConverterGAST
import re
import subprocess
import os
import tempfile

def convert_to_python(code):
    """Converts the custom mini-language to standard Python syntax."""
    lines = code.splitlines()
    python_lines = []
    for line in lines:
        # Preserve indentation
        indent = len(line) - len(line.lstrip())
        line = line.strip()

        # Skip empty lines
        if not line:
            python_lines.append("")
            continue

        # Replace := with =
        line = line.replace(":=", "=")

        # Remove semicolons
        line = line.rstrip(";")

        # Replace whileloop with while and remove parentheses
        if line.startswith("whileloop"):
            line = line.replace("whileloop", "while", 1)
            # Remove parentheses around the condition
            condition = line[line.find("(")+1:line.rfind(")")].strip()
            line = f"while {condition}:"

        # Replace forloop with for and remove parentheses
        if line.startswith("forloop"):
            line = line.replace("forloop", "for", 1)
            # Extract the for loop condition (e.g., "i in range(2)")
            for_match = re.match(r'for\s+(\w+)\s+in\s+range\((\d+)\)', line)
            if for_match:
                loop_var, range_val = for_match.groups()
                line = f"for {loop_var} in range({range_val}):"
            else:
                raise ValueError(f"Invalid forloop syntax: {line}")

        # Remove parentheses from if statements
        if line.startswith("if"):
            condition = line[line.find("(")+1:line.rfind(")")].strip()
            line = f"if {condition}:"

        # Reapply indentation
        python_lines.append(" " * indent + line)

    return "\n".join(python_lines)

def parse_ssa_file(file_content):
    """Parse SSA content directly from string instead of file."""
    lines = file_content.split('\n')
    ssa_lines = [line.strip() for line in lines if line.strip() and not line.strip().startswith("#") and line.strip() != "else"]
    return ssa_lines

def parse_expression(expr):
    """Parses an SSA expression and converts it to SMT-LIB format."""
    comp_match = re.match(r'^(\w+_\d+)\s*(>|<)\s*(\w+_\d+)$', expr)
    if comp_match:
        left, op, right = comp_match.groups()
        return f"({op} {left} {right})"

    comp_const_match = re.match(r'^(\w+_\d+)\s*(>|<)\s*(\d+)$', expr)
    if comp_const_match:
        left, op, right = comp_const_match.groups()
        return f"({op} {left} {right})"

    arith_match = re.match(r'^(\w+_\d+)\s*(\+|-|\*|\/)\s*(\w+_\d+|\d+)$', expr)
    if arith_match:
        left, op, right = arith_match.groups()
        return f"({op} {left} {right})"

    ternary_match = re.match(r'^(\w+_\d+)\s*\?\s*(\w+_\d+)\s*:\s*(\w+_\d+)$', expr)
    if ternary_match:
        cond, true_val, false_val = ternary_match.groups()
        return f"(ite {cond} {true_val} {false_val})"

    return expr

def extract_vars(expr):
    """Extracts all variables from an expression."""
    vars = set(re.findall(r'\b\w+_\d+\b', expr))
    ternary_match = re.match(r'^(\w+_\d+)\s*\?\s*(\w+_\d+)\s*:\s*(\w+_\d+)$', expr)
    if ternary_match:
        cond, true_val, false_val = ternary_match.groups()
        vars.add(cond)
        vars.add(true_val)
        vars.add(false_val)
    return vars

def convert_to_smt(ssa_lines, user_assertion):
    smt_decls = set()
    smt_asserts = []
    var_types = {}

    for line in ssa_lines:
        indent_level = len(line) - len(line.lstrip())
        line = line.strip()

        assign_match = re.match(r'^(\w+_\d+)\s*=\s*(.+)$', line)
        if assign_match:
            var, expr = assign_match.groups()
            if 'c_' in var:
                var_types[var] = 'Bool'
            else:
                var_types[var] = 'Int'
            smt_expr = parse_expression(expr)
            smt_asserts.append(f"(assert (= {var} {smt_expr}))")
            smt_decls.add(var)
            smt_decls.update(extract_vars(expr))
            continue

        phi_match = re.match(r'^(\w+_\d+)\s*=\s*(\w+_\d+)\s*\?\s*(\w+_\d+)\s*:\s*(\w+_\d+)$', line)
        if phi_match:
            var, cond, true_val, false_val = phi_match.groups()
            var_types[var] = var_types.get(var, 'Int')
            var_types[cond] = 'Bool'
            smt_asserts.append(f"(assert (= {var} (ite {cond} {true_val} {false_val})))")
            smt_decls.add(var)
            smt_decls.add(cond)
            smt_decls.add(true_val)
            smt_decls.add(false_val)
            continue

    smt_output = ["(set-logic QF_LIA)"]
    for var in sorted(smt_decls):
        var_type = var_types.get(var, 'Int')
        smt_output.append(f"(declare-const {var} {var_type})")

    smt_output.extend(smt_asserts)
    if user_assertion:
        smt_output.append(user_assertion)
    smt_output.extend(["(check-sat)", "(get-model)"])

    return "\n".join(smt_output)

def run_z3(smt_content):
    """Runs Z3 on SMT content directly."""
    try:
        # Create a temporary file in a secure way
        with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as temp_file:
            temp_file.write(smt_content)
            temp_file_path = temp_file.name

        try:
            result = subprocess.run(['z3', temp_file_path], capture_output=True, text=True, timeout=10)
            output = result.stdout.strip()
            if "sat" in output:
                status = "sat"
                model_lines = []
                capturing_model = False
                for line in output.splitlines():
                    if line.startswith("(model"):
                        capturing_model = True
                    if capturing_model:
                        model_lines.append(line)
                    if line.startswith(")"):
                        capturing_model = False
                model = "\n".join(model_lines)
            elif "unsat" in output:
                status = "unsat"
                model = "No model (unsat)"
            else:
                status = "unknown"
                model = "Unknown result"
            return status, model
        finally:
            # Clean up the temporary file
            os.unlink(temp_file_path)
    except subprocess.TimeoutExpired:
        return "timeout", "Z3 timed out"
    except Exception as e:
        return "error", f"Z3 error: {str(e)}"

def process_code(code, loop_bound, user_assertion=None):
    """Processes a single code snippet to SSA and SMT."""
    try:
        # Convert mini-language to Python
        python_code = convert_to_python(code)

        # Convert Python to GAST AST
        tree = gast.parse(python_code)

        # Convert to SSA
        converter = SSAConverterGAST(loop_bound=loop_bound)
        converter.visit(tree)
        ssa_output = "\n".join(converter.output)

        # Convert SSA to SMT directly
        ssa_lines = parse_ssa_file(ssa_output)
        smt_code = convert_to_smt(ssa_lines, user_assertion)

        # Run Z3 on the SMT content
        status, model = run_z3(smt_code)

        return {
            "ssa": ssa_output,
            "smt": smt_code,
            "status": status,
            "model": model
        }
    except Exception as e:
        return {
            "ssa": "",
            "smt": "",
            "status": "error",
            "model": f"Error processing code: {str(e)}"
        }