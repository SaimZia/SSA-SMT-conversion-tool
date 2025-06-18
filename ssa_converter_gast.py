import gast

class SSAConverterGAST(gast.NodeVisitor):
    def __init__(self, loop_bound=3):
        self.env = {}  # Tracks scalar variables
        self.counter = {}  # Tracks version numbers
        self.output = []  # Stores SSA output
        self.indent_level = 0
        self.array_elements = {}  # Tracks SSA variables for array indices
        self.loop_bound = loop_bound  # Configurable loop unrolling limit

    def fresh_var(self, name, index=None):
        """Generates a fresh SSA variable name with optional index."""
        base_name = f"{name}{index}" if index is not None else name
        self.counter.setdefault(base_name, 0)
        self.counter[base_name] += 1
        var = f"{base_name}_{self.counter[base_name]}"
        if index is not None:
            self.array_elements[(name, index)] = var
        else:
            self.env[name] = var
        return var

    def get_var(self, name, index=None):
        """Gets the variable's SSA name, creating it if not exists."""
        if index is not None:
            key = (name, index)
            if key in self.array_elements:
                return self.array_elements[key]
            return self.fresh_var(name, index)
        return self.env.get(name, name)

    def indent(self):
        """Returns the current indentation."""
        return "    " * self.indent_level

    def visit_Module(self, node):
        """Visits the module (program body)."""
        for stmt in node.body:
            self.visit(stmt)

    def visit_Assign(self, node):
        """Visits assignment statements, including array assignments."""
        if isinstance(node.targets[0], gast.Subscript):
            array = node.targets[0].value.id
            index = self.visit(node.targets[0].slice)
            # If index is a BinOp or variable, resolve it
            if isinstance(index, str) and any(op in index for op in ['+', '-', '*', '/']):
                index_parts = index.split()
                base_index = self.get_var(index_parts[0] if ' ' in index else index)
                index_value = int(base_index.split('_')[-1]) if '_' in base_index else 0
                if len(index_parts) > 1:
                    op, offset = index_parts[1], int(index_parts[2])
                    if op == '+':
                        index_value += offset
            else:
                index_value = int(index) if index.isdigit() else int(self.get_var(index.split('_')[0]).split('_')[-1])
            value = self.visit(node.value)
            new_var = self.fresh_var(array, index_value)
            self.output.append(f"{self.indent()}{new_var} = {value}")
        else:
            target = node.targets[0].id
            value = self.visit(node.value)
            # Skip assignment if value is an empty string (signal from visit_List)
            if value is not None and value != "":
                new_var = self.fresh_var(target)
                self.output.append(f"{self.indent()}{new_var} = {value}")
                self.env[target] = new_var

    def visit_Name(self, node):
        """Visits name (variables)."""
        if isinstance(node.ctx, gast.Load):
            return self.get_var(node.id)
        return node.id

    def visit_Constant(self, node):
        """Visits constant values."""
        return repr(node.value)

    def visit_BinOp(self, node):
        """Visits binary operations."""
        left = self.visit(node.left)
        right = self.visit(node.right)
        op = self.visit(node.op)
        if op is None:
            raise ValueError(f"Operator visit returned None for {node.op}")
        return f"{left} {op} {right}"

    def visit_If(self, node):
        """Handles if-statements and introduces phi functions, works inside loops."""
        cond = self.visit(node.test)
        cond_var = self.fresh_var("c")
        self.output.append(f"{self.indent()}{cond_var} = {cond}")

        # Save current env and array_elements
        old_env = self.env.copy()
        old_array_elements = self.array_elements.copy()

        # THEN branch
        self.indent_level += 1
        self.env = old_env.copy()
        self.array_elements = old_array_elements.copy()
        self.visit_block(node.body)
        then_env = self.env.copy()
        then_array_elements = self.array_elements.copy()
        self.indent_level -= 1

        # ELSE branch
        self.indent_level += 1
        self.env = old_env.copy()
        self.array_elements = old_array_elements.copy()
        self.visit_block(node.orelse)
        else_env = self.env.copy()
        else_array_elements = self.array_elements.copy()
        self.indent_level -= 1

        # Merge variables using phi functions
        merged_vars = set(then_env.keys()) | set(else_env.keys())
        for var in merged_vars:
            t = then_env.get(var, self.get_var(var.split('_')[0]) if var in old_env else self.fresh_var(var.split('_')[0]))
            e = else_env.get(var, self.get_var(var.split('_')[0]) if var in old_env else self.fresh_var(var.split('_')[0]))
            if t != e:
                merged_var = self.fresh_var(var.split('_')[0])
                self.output.append(f"{self.indent()}{merged_var} = {cond_var} ? {t} : {e}")
                self.env[var] = merged_var

        # Merge array elements
        merged_indices = set(then_array_elements.keys()) | set(else_array_elements.keys())
        for (name, index) in merged_indices:
            t = then_array_elements.get((name, index), self.get_var(name, index))
            e = else_array_elements.get((name, index), self.get_var(name, index))
            if t != e:
                merged_var = self.fresh_var(name, index)
                self.output.append(f"{self.indent()}{merged_var} = {cond_var} ? {t} : {e}")
                self.array_elements[(name, index)] = merged_var

    def visit_For(self, node):
        """Handles for loops and unrolls them."""
        target = node.target.id
        for i in range(self.loop_bound):
            new_var = self.fresh_var(target)
            self.output.append(f"{self.indent()}{new_var} = {i}")

            self.indent_level += 1
            self.visit_block(node.body)
            self.indent_level -= 1

    def visit_While(self, node):
        """Handles while loops with proper SSA phi functions."""
        old_env = self.env.copy()
        old_array_elements = self.array_elements.copy()
        
        prev_x_var = self.get_var('x') if 'x' in self.env else 'x_0'
        x_vars = [prev_x_var]
        cond_vars = []

        for i in range(self.loop_bound):
            cond = self.visit(node.test)
            cond_var = self.fresh_var("c")
            cond_vars.append(cond_var)
            self.output.append(f"{self.indent()}{cond_var} = {cond}")

            self.indent_level += 1
            self.visit_block(node.body)
            self.indent_level -= 1

            current_x_var = self.get_var('x')
            x_vars.append(current_x_var)

            self.env = old_env.copy()
            self.env['x'] = current_x_var
            self.array_elements = old_array_elements.copy()

        final_x_var = x_vars[0]
        for i in range(self.loop_bound):
            new_x_var = self.fresh_var('x')
            self.output.append(f"{self.indent()}{new_x_var} = {cond_vars[i]} ? {x_vars[i+1]} : {final_x_var}")
            final_x_var = new_x_var

        self.env['x'] = final_x_var

    def visit_block(self, stmts):
        """Visits a block of statements."""
        for stmt in stmts:
            self.visit(stmt)

    def visit_Compare(self, node):
        """Visits comparisons."""
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        op = self.visit(node.ops[0])
        if op is None:
            raise ValueError(f"Operator visit returned None for {node.ops[0]}")
        return f"{left} {op} {right}"

    def visit_Add(self, _): return "+"
    def visit_Gt(self, _): return ">"
    def visit_Lt(self, _): return "<"

    def visit_Subscript(self, node):
        """Visits array indexing, returning SSA variable for the element."""
        array = self.visit(node.value).rstrip('_')
        index = self.visit(node.slice)
        # Resolve index to an integer value based on the current loop context
        if isinstance(index, str) and any(op in index for op in ['+', '-', '*', '/']):
            index_parts = index.split()
            base_index = self.get_var(index_parts[0] if ' ' in index else index)
            index_value = int(base_index.split('_')[-1]) if '_' in base_index else 0
            if len(index_parts) > 1:
                op, offset = index_parts[1], int(index_parts[2])
                if op == '+':
                    index_value += offset
        else:
            index_value = int(index) if index.isdigit() else int(self.get_var(index.split('_')[0]).split('_')[-1])
        return self.get_var(array, index_value)

    def visit_List(self, node):
        """Visits list literals (e.g., [1, 2, 3, 4])."""
        elements = [self.visit(elt) for elt in node.elts]
        for i, elem in enumerate(elements):
            new_var = self.fresh_var('arr', i)
            self.output.append(f"{self.indent()}{new_var} = {elem}")
        # Return empty string to signal visit_Assign to skip the assignment
        return ""