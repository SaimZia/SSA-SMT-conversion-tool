from flask import Flask, request, jsonify
from your_script import process_code

app = Flask(__name__)

from flask_cors import CORS
CORS(app)

@app.route('/validate', methods=['POST'])
def validate():
    try:
        data = request.get_json()
        code = data['code']
        loop_bound = int(data['loop_bound'])
        user_assertion = data['assertion']

        # Validate loop bound
        if not 1 <= loop_bound <= 5:
            return jsonify({"error": "Loop bound must be between 1 and 5"}), 400

        result = process_code(code, loop_bound, user_assertion)
        return jsonify(result)
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/equivalence', methods=['POST'])
def equivalence():
    try:
        data = request.get_json()
        code1 = data['code1']
        code2 = data['code2']
        loop_bound = int(data['loop_bound'])
        user_assertion = data['assertion']

        # Validate loop bound
        if not 1 <= loop_bound <= 5:
            return jsonify({"error": "Loop bound must be between 1 and 5"}), 400

        # Process both codes
        result1 = process_code(code1, loop_bound, None)  # No assertion yet
        result2 = process_code(code2, loop_bound, None)

        # Combine SMT codes with a shared assertion for equivalence
        # For equivalence, we check if the final states are the same
        # We need to rename variables in the second program to avoid conflicts
        smt1_lines = result1['smt'].splitlines()
        smt2_lines = result2['smt'].splitlines()

        # Rename variables in the second SMT code (e.g., arr0_1 -> arr0_1_b)
        smt2_lines = [line.replace('arr', 'arr_b').replace('x_', 'x_b_').replace('c_', 'c_b_').replace('i_', 'i_b_').replace('temp_', 'temp_b_') for line in smt2_lines]

        # Combine SMT codes
        combined_smt = ["(set-logic QF_LIA)"]
        # Declarations and assertions from both programs
        combined_smt.extend([line for line in smt1_lines if line.startswith("(declare-const")])
        combined_smt.extend([line for line in smt2_lines if line.startswith("(declare-const")])
        combined_smt.extend([line for line in smt1_lines if line.startswith("(assert")])
        combined_smt.extend([line for line in smt2_lines if line.startswith("(assert")])

        # Add equivalence assertion
        # For simplicity, assume we're comparing the final value of 'x'
        # In a real application, you might need to compare more variables or use a more sophisticated equivalence check
        final_x1 = max([v for v in result1['ssa'].splitlines() if 'x_' in v], key=lambda v: int(v.split('x_')[1].split(' ')[0]))
        final_x2 = max([v for v in result2['ssa'].splitlines() if 'x_' in v], key=lambda v: int(v.split('x_')[1].split(' ')[0]))
        final_x1_var = final_x1.split('=')[0].strip()
        final_x2_var = final_x2.split('=')[0].strip().replace('x_', 'x_b_')
        equiv_assertion = f"(assert (= {final_x1_var} {final_x2_var}))"

        # Add user assertion (apply to both programs' variables)
        if user_assertion:
            user_assertion_b = user_assertion.replace('arr', 'arr_b').replace('x_', 'x_b_').replace('c_', 'c_b_').replace('i_', 'i_b_').replace('temp_', 'temp_b_')
            combined_smt.append(user_assertion)
            combined_smt.append(user_assertion_b)

        combined_smt.append(equiv_assertion)
        combined_smt.extend(["(check-sat)", "(get-model)"])

        combined_smt_code = "\n".join(combined_smt)

        # Write combined SMT to a temporary file
        with open("temp_equiv_smt.smt2", "w") as f:
            f.write(combined_smt_code)

        # Run Z3
        status, model = process_code(code1, loop_bound)['status'], process_code(code1, loop_bound)['model']  # Reuse run_z3
        status, model = run_z3("temp_equiv_smt.smt2")

        # Clean up
        os.remove("temp_equiv_smt.smt2")

        return jsonify({
            "program1": result1,
            "program2": result2,
            "combined_smt": combined_smt_code,
            "status": status,
            "model": model
        })
    except Exception as e:
        return jsonify({"error": str(e)}), 500

if __name__ == "__main__":
    app.run(debug=True, port=5000)