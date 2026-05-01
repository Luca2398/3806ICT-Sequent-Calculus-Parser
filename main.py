# Libraries
import time
from pathlib import Path
from collections import deque

rules_applied = 0


# File handling
def load_file(fileName):
    # Error handling for opening file
    try:
        with open(fileName, 'r') as file:
            content = file.read()
            # print(content) # Error handling
    # Return error if file of input file name is not found
    except FileNotFoundError:
        print(f"File '{fileName}' was not found.")
        exit()
    return content

# Function for printing the entire proof (tree)
def print_proof(node, depth=0):
    # Added indent to printed child nodes for readability
    indent = "    " * (depth)
    if node.is_closed == True:
        print(f"{indent}{node.data} closed by {node.closed_by}")
    else:
        if not node.rule_app:
            print(f"{indent}{node.data}")
        else:
            print(f"{indent}{node.data} ({node.rule_app[0]})")
            
    # Recursion for printing the children nodes of the child node
    for child in node.children:
        print_proof(child, depth + 1)

# Function for obtaining all leaf nodes of the argument node using DFS
def get_leaf_nodes(node):
    # Append all found leaf nodes to list
    leaves = []
    # If no children, the node is a leaf
    if not node.children:
        return [node]
    for child in node.children:
        leaves.extend(get_leaf_nodes(child))
    return leaves

# Remove outermost parentheses
def strip_outer(expr):
    expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        return expr[1:-1]
    return expr

# Function to find main connective in proof formula
def find_main_connective(expr):
    depth = 0
    i = 0

    while i < len(expr):
        # Skip quantifiers
        if expr[i] in ["!", "?"]:
            # Skip until ":"
            while i < len(expr) and expr[i] != ":":
                i += 1
            i += 1
            continue

        if expr[i] == "(":
            depth += 1
        elif expr[i] == ")":
            depth -= 1
        
        # Only care at top level
        elif depth == 0:
            # Equivalence
            if expr[i:i+3] == "<=>":
                return i, "<=>"

            # Implication
            if expr[i:i+2] == "=>":
                return i, "=>"

            # Binary connectives
            if expr[i] in {"&", "|"}:
                return i, expr[i]
            
            # Negation
            if expr[i] == "~":
                return i, "~"
            
        i += 1

    return -1, None

def parse(expr):
    expr = expr.replace(" ", "")
    expr = strip_outer(expr)

    # Negation (UNARY case)
    if expr.startswith("~"):
        inner = parse(expr[1:])
        if inner is None:
            raise ValueError(f"Bad negation: {expr}")
        return Negation(inner)

    # Quantifier
    # Universal quantifier
    if expr.startswith("!"):
        var_end = expr.index(":")
        vars_part = expr[2:var_end]
        vars_part = vars_part.replace("[", "").replace("]", "").strip()
        body = expr[var_end+1:]
        return Quantifier("forall", vars_part, parse(body))
    # Existential quantifier
    if expr.startswith("?"):
        var_end = expr.index(":")
        vars_part = expr[2:var_end]
        vars_part = vars_part.replace("[", "").replace("]", "").strip()
        body = expr[var_end+1:]
        return Quantifier("exists", vars_part, parse(body))
    
    # Atom check
    idx, op = find_main_connective(expr)

    if op is None:
        # For predicate like p(X,Y)
        if "(" in expr:
            name = expr[:expr.index("(")]
            start = expr.index("(") + 1
            end = expr.rfind(")")
            args_str = expr[start:end].strip()
            if not args_str:
                args = []
            else:
                args = [Var(a.strip()) for a in args_str.split(",") if a.strip()]
            return Predicate(name, args)
        else:
            return Predicate(expr, [])
    
    if op == "<=>":
        left = parse(expr[:idx])
        right = parse(expr[idx+3:])
        return Connective("&", 
                Connective("=>", left, right),
                Connective("=>", right, left))
    elif op == "=>":
        left = expr[:idx]
        right = expr[idx+2:]
    else:
        left = expr[:idx]
        right = expr[idx+1:]

    return Connective(op, parse(left), parse(right))

def collect_atoms(node):
    if node is None:
        return set()
    
    if isinstance(node, Predicate):
        return {(node.name, tuple(node.args))}

    if isinstance(node, Connective):
        return collect_atoms(node.left) | collect_atoms(node.right)

    if isinstance(node, Quantifier):
        return collect_atoms(node.body)

    if isinstance(node, list):
        atoms = set()
        for n in node:
            atoms |= collect_atoms(n)
        return atoms

    return set()

def collect_vars(node):
    vars = set()

    if isinstance(node, Var):
        vars.add(node.name)
    
    if isinstance(node, Predicate):
        for arg in node.args:
            vars |= collect_vars(arg)
    
    if isinstance(node, Connective):
        vars |= collect_vars(node.left)
        vars |= collect_vars(node.right)
    
    if isinstance(node, Quantifier):
        vars.add(node.var)
        vars |= collect_vars(node.body)
    
    if isinstance(node, list):
        for n in node:
           vars |= collect_vars(n)
    
    return vars

def collect_terms(node):
    terms = set()

    if isinstance(node, Const):
        terms.add(node.name)

    if isinstance(node, Predicate):
        for arg in node.args:
            terms |= collect_terms(arg)
    
    if isinstance(node, Connective):
        terms |= collect_terms(node.left)
        terms |= collect_terms(node.right)

    if isinstance(node, Quantifier):
        terms |= collect_terms(node.body)

    if isinstance(node, list):
        for n in node:
            terms |= collect_terms(n)
    
    return terms

def collect_all_terms(node):
    terms = set()

    if isinstance(node, ProofNode):
        terms |= collect_all_terms(node.data)
        for c in node.children:
            terms|= collect_all_terms(c)

    elif isinstance(node, FormulaNode):
        terms |= collect_terms(node.left)
        terms |= collect_terms(node.right)

    return terms

def substitute(node, var, replacement):
    if isinstance(node, Var):
        if node.name == var:
            
            return replacement 
        
        return node
    
    if isinstance(node, Const):
        return node
    
    if isinstance(node, Predicate):
        return Predicate(node.name, [substitute(arg, var, replacement) for arg in node.args])
        

    if isinstance(node, Connective):
        return Connective(
            node.op,
            substitute(node.left, var, replacement),
            substitute(node.right, var, replacement)
        )
    
    if isinstance(node, Quantifier):
        if node.var == var:
            return node
        return Quantifier(node.qtype, node.var, substitute(node.body, var, replacement))
    
    return node

def fresh_var(node):
    used = collect_all_terms(node)

    i = 1
    while True:
        candidate = f"t_{i}"
        if candidate not in used:
            return Var(candidate)
        i += 1

def fresh_const(node):
    used = set()

    used |= collect_vars(node.left)
    used |= collect_vars(node.right)

    i = 1
    while True:
        candidate = f"c_{i}"
        if candidate not in used:
            return Const(candidate)
        i += 1

def open_leaves(node):
    return [leaf for leaf in get_leaf_nodes(node) if not leaf.is_closed]



# ---------- LK' proof rules ----------
# Identity
def id(node):
    global rules_applied
    leaf = node

    left_atoms = collect_atoms(leaf.data.left)
    right_atoms = collect_atoms(leaf.data.right)

    common = left_atoms & right_atoms

    if common:
        leaf.is_closed = True
        leaf.closed_by = "id"
        rules_applied += 1
        return True
    return False

# Right true
def true_r(node):
    global rules_applied
    leaf = node
    right = leaf.data.right

    if any(isinstance(x, Predicate) and x.name == "$true" for x in right):
        leaf.is_closed = True
        leaf.closed_by = "true R"
        rules_applied += 1
        return True
    return False

# Left false
def false_l(node):
    global rules_applied
    leaf = node
    left = leaf.data.left

    if any(isinstance(x, Predicate) and x.name == "$false" for x in left):
        leaf.is_closed = True
        leaf.closed_by = "false L"
        rules_applied += 1
        return True
    return False

# Left conjunction
def conj_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Connective) and expr.op == "&":

            A = expr.left
            B = expr.right

            rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]

            new_left = rest_left + [A, B]

            leaf.children.append(ProofNode(FormulaNode(new_left, formula.right)))
            leaf.rule_app.append("conj_l")

            rules_applied += 1
            return True
    return False


# Right conjunction
def conj_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data
    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Connective) and expr.op == "&":
            
            A = expr.left
            B = expr.right

            rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]

            new_left1 = formula.left
            new_right1 = [A] + rest_right

            new_left2 = formula.left
            new_right2 = [B] + rest_right

            leaf.children.append(ProofNode(FormulaNode(new_left1, new_right1)))
            leaf.children.append(ProofNode(FormulaNode(new_left2, new_right2)))
            leaf.rule_app.append("conj_r")

            rules_applied += 1
            return True
    return False

# Left disjunction
def disj_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data
    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Connective) and expr.op == "|":
            
            A = expr.left
            B = expr.right

            rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]

            new_left1 = rest_left + [A]
            new_right1 = formula.right

            new_left2 = rest_left + [B]
            new_right2 = formula.right

            leaf.children.append(ProofNode(FormulaNode(new_left1, new_right1)))
            leaf.children.append(ProofNode(FormulaNode(new_left2, new_right2)))
            leaf.rule_app.append("disj_l")

            rules_applied += 1
            return True
    return False

# Right disjunction
def disj_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Connective) and expr.op == "|":

            A = expr.left
            B = expr.right

            rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]

            new_right = [A, B] + rest_right

            leaf.children.append(ProofNode(FormulaNode(formula.left, new_right)))
            leaf.rule_app.append("disj_r")

            rules_applied += 1
            return True
    return False

# Left negation
def negation_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Negation):

            A = expr.child

            rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]

            new_right = [A] + formula.right

            leaf.children.append(ProofNode(FormulaNode(rest_left, new_right)))
            leaf.rule_app.append("negation_l")

            rules_applied += 1
            return True
    return False

# Right negation
def negation_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Negation):
            A = expr.child

            rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]

            new_left = formula.left + [A]

            leaf.children.append(ProofNode(FormulaNode(new_left, rest_right)))
            leaf.rule_app.append("negation_r")

            rules_applied += 1
            return True
    return False

# Left implication
def imp_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data
    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Connective) and expr.op == "=>":
            
            A = expr.left
            B = expr.right

            rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]

            new_left1 = rest_left
            new_right1 = formula.right + [A]

            new_left2 = rest_left + [B]
            new_right2 = formula.right

            leaf.children.append(ProofNode(FormulaNode(new_left1, new_right1)))
            leaf.children.append(ProofNode(FormulaNode(new_left2, new_right2)))
            leaf.rule_app.append("imp_l")

            rules_applied += 1
            return True
    return False

# Right implication
def imp_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data
    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Connective) and expr.op == "=>":

            A = expr.left
            B = expr.right

            new_left = formula.left + [A]
            new_right = formula.right[:f_idx] + [B] + formula.right[f_idx+1:]

            leaf.children.append(ProofNode(FormulaNode(new_left, new_right)))
            leaf.rule_app.append("imp_r")
                
            rules_applied += 1
            return True
    return False

# Left universal
def univ_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Quantifier) and expr.qtype == "forall":

            terms = collect_terms(formula.left) | collect_terms(formula.right)

            new_children = []

            if terms:
                # Instantiate with existing terms
                for t in terms:
                    term_obj = Const(t)
                    instantiated = substitute(expr.body, expr.var, term_obj)
                    
                    rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]
                    new_left = rest_left + [instantiated]

                    new_children.append(ProofNode(FormulaNode(new_left, formula.right)))

            else:
                fresh = fresh_var(leaf)
                instantiated = substitute(expr.body, expr.var, fresh)

                rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]
                new_left = rest_left + [instantiated]

                new_children.append(ProofNode(FormulaNode(new_left, formula.right)))

            leaf.children.extend(new_children)
            leaf.rule_app.append("univ_l")

            rules_applied += 1
            return True
    return False

# Right universal
def univ_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data
    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Quantifier) and expr.qtype == "forall":
            fresh = fresh_var(leaf)
            instantiated = substitute(expr.body, expr.var, fresh)

            rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]
            new_right = [instantiated] + rest_right

            leaf.children.append(ProofNode(FormulaNode(formula.left, new_right)))
            leaf.rule_app.append("univ_r")

            rules_applied += 1
            return True
    return False

# Left existential
def exis_l(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.left):
        if isinstance(expr, Quantifier) and expr.qtype == "exists":

            fresh = fresh_var(leaf)
            instantiated = substitute(expr.body, expr.var, fresh)

            rest_left = formula.left[:f_idx] + formula.left[f_idx+1:]
            new_left = rest_left + [instantiated]

            leaf.children.append(ProofNode(FormulaNode(new_left, formula.right)))
            leaf.rule_app.append("exis_l")

            rules_applied += 1
            return True
    return False

# Right existential
def exis_r(node):
    global rules_applied
    leaf = node
    formula = leaf.data

    for f_idx, expr in enumerate(formula.right):
        if isinstance(expr, Quantifier) and expr.qtype == "exists":

            terms = collect_terms(formula.left) | collect_terms(formula.right)

            new_children = []

            if terms:
                # Instantiate with existing terms
                for t in terms:
                    term_obj = Const(t)
                    instantiated = substitute(expr.body, expr.var, term_obj)
                    
                    rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]
                    new_right = [instantiated] + rest_right

                    new_children.append(ProofNode(FormulaNode(formula.left, new_right)))

            else:
                fresh = fresh_var(leaf)
                instantiated = substitute(expr.body, expr.var, fresh)

                rest_right = formula.right[:f_idx] + formula.right[f_idx+1:]
                new_right = [instantiated] + rest_right

                new_children.append(ProofNode(FormulaNode(formula.left, new_right)))

            leaf.children.extend(new_children)
            leaf.rule_app.append("exis_r")

            rules_applied += 1
            return True
    return False
    


# ---------- STRATEGIES ----------
def naiive_strat(proof, max_steps=1000):
    steps = 0
    worklist = deque(open_leaves(proof))
    
    while worklist and steps < max_steps:
        node = worklist.popleft()

        if node.is_closed:
            continue
        
        progress = False
        
        if node.is_closed:
            continue

        node._touched = getattr(node, "_touched", 0)

        # 1. Closers
        if id(node) or true_r(node) or false_l(node):
            node.is_closed = True
            node.closed_by = "close rule"
            progress = True

        # 2. Unary rules
        elif (
            imp_r(node) or
            conj_l(node) or
            disj_r(node) or
            negation_l(node) or
            negation_r(node) or
            univ_r(node) or
            exis_l(node)
        ):
            progress = True

        # 3. Binary rules
        elif (
            imp_l(node) or
            conj_r(node) or
            disj_l(node)
        ):
            progress = True

        # 4. Quantifier instantiation
        elif (
            univ_l(node) or
            exis_r(node)
        ):
            progress = True
        
        # if nothing applied anywhere
        if progress:
            worklist.extend(open_leaves(node))
            
        steps += 1

    print("Stopped: max steps reached.")

    return proof

def iterative_deepening(left, right, max_depth_limit):
    for depth in range(max_depth_limit):
        formula = FormulaNode(left, right)
        proof = ProofNode(formula)

        result = depth_limit_strat(proof, depth)

        if all(leaf.is_closed for leaf in get_leaf_nodes(result)):
            print(f"PROOF FOUND at depth {depth}")
            return result
    
    print("FAILED within depth limit")
    return proof

def depth_limit_strat(proof, max_depth):
    worklist = deque([(proof, 0)])
    
    while worklist:
        node, depth = worklist.popleft()

        if depth > max_depth:
            continue

        if node.is_closed:
            continue
        
        progress = False

        # 1. Closers
        if id(node) or true_r(node) or false_l(node):
            node.is_closed = True
            node.closed_by = "close rule"
            progress = True

        # 2. Unary rules
        elif (
            imp_r(node) or
            conj_l(node) or
            disj_r(node) or
            negation_l(node) or
            negation_r(node) or
            univ_r(node) or
            exis_l(node)
        ):
            progress = True

        # 4. Binary rules
        elif (
            imp_l(node) or
            conj_r(node) or
            disj_l(node)
        ):
            progress = True

        # 3. Quantifier instantiation
        elif (
            univ_l(node) or
            exis_r(node)
        ):
            progress = True
        
        # if nothing applied anywhere
        if progress:
            for leaf in open_leaves(node):
                worklist.append((leaf, depth + 1))

    return proof



# ---------- CLASSES ----------
# Class for saving proof tree structure (N-ary tree data structure)
class ProofNode:
    def __init__(self, data):
        self.data = data
        self.children = []
        # Attributes to contain proof closed status of node
        self.is_closed = False
        self.closed_by = None
        self.rule_app = []

    # Class function for returning/outputting the tree
    def __repr__(self):
        if self.data is None:
            return str(self.data)
        return f"{self.data} {self.children}"

# Class for storing logic formulae (binary tree data structure)
class FormulaNode:
    def __init__(self, left=None, right=None):
        self.symbol = "|-"
        self.left = left or []        # LHS of turnstile
        self.right = right or []      # RHS of turnstile

    # Class function for returning/outputting the tree
    def __repr__(self):
        return f"{self.left} {self.symbol} {self.right}"

# Contains atomic elements in the proofs
class Term:
    pass

class Var:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

class Const:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

class Predicate:
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __repr__(self):
        return f"{self.name}({', '.join(map(str, self.args))})"

class Negation:
    def __init__(self, child):
        self.child = child

    def __repr__(self):
        return f"~{self.child}"

# Connectives for atoms such as &, |, etc are stored
class Connective:
    def __init__(self, op, left=None, right=None):
        self.op = op        # Operator
        self.left = left    # LHS
        self.right = right  # RHS
    
    def __repr__(self):
        if self.op == "~":
            return f"~{self.left}"
        return f"({self.left} {self.op} {self.right})"

# Specifically for quantifiers as they introduce variables and scope
class Quantifier:
    def __init__(self, qtype, var, body):
        self.qtype = qtype # forall / exists
        self.var = var
        self.body = body

    def __repr__(self):
        return f"{self.qtype}{self.var}({self.body})"



# ---------- MAIN ----------
# Prompt user for name of file containing the logic formulas
# fileName = input("File Name: ").strip()
# fileName = "PUZ001+1.txt"

for file in Path("./Problems").iterdir():
    if not file.is_file():
        continue

    axioms = []
    conjectures = []

    fileName = file
    content = load_file(fileName)

    rules_applied = 0
    problems = []
    buffer = ""
    current_name = None

    for line in content.splitlines():
        line = line.strip()

        if not line or line.startswith("%"):
            continue # Skip comments

        if not line: 
            continue # Skip if empty line

        buffer += " " + line # Accumulate lines

        if "." not in line:
            continue

        formula_str = buffer.strip().rstrip(".")
        buffer = "" # Reset buffer for next formula

        if "fof(" not in formula_str:
            continue

        inner = formula_str[4:-1] # Remove "fof(" and final ")"
        parts = [p.strip() for p in inner.split(",", 2)] # Split list into 3 elements
        if len(parts) != 3:
            print("Skipping malformed fof:", formula_str)
            continue
        name, role, logic = parts
        parsed = parse(logic)
        current_name = name

        if role == "axiom":
            axioms.append(parsed)
        elif role == "conjecture":
            problems.append((axioms.copy(), [parsed], name))
            axioms = []   # reset for next independent proof



    for i, (left, right, name) in enumerate(problems):
        start = time.perf_counter()

        print("\nProcessing file::", fileName)

        # print(F"\n=== Proof {i+1}: {name} ===")
        
        formula = FormulaNode(left, right)
        proof = ProofNode(formula)

        search_depth = 10
        # result_proof = naiive_strat(proof)
        result_proof = iterative_deepening(left, right, search_depth)
        # print_proof(proof)

        if all(leaf.is_closed for leaf in get_leaf_nodes(result_proof)):
            print("Result: CLOSED")
        else:
            print("Result: OPEN")
        
        print(f"TOTAL STEPS: {rules_applied}")

        end = time.perf_counter()
        print(f"EXECUITON TIME: {end - start:.6f} seconds")