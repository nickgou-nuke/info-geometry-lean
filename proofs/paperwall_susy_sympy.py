"""SymPy witness for the Paperwall Holography SUSY Superalgebra.

We construct a Supersymmetry (SUSY) algebra strictly out of:
1. Holographic Cuntz algebra boundary operators (S1, S2).
2. Chiral glide reflections (G) from the 2D CFT paperwall symmetry.

By mapping the fermion operators into the Cuntz algebra:
   c  = S_2 S_1^*
   c† = S_1 S_2^*
We bind the glide reflection G to the fermion to construct the supercharge Q:
   Q = c * G
"""

import sympy as sp

# We don't use SymPy's algebra for non-commutative words because it can arbitrarily reorder them
# in nested expressions. We will use a custom string-based word reducer for exact algebra.

def reduce_word(w):
    """Reduces a word (list of strings) according to Cuntz and Glide relations."""
    changed = True
    while changed:
        changed = False
        for i in range(len(w)-1):
            pair = (w[i], w[i+1])
            # Isometries
            if pair in [("S1*", "S1"), ("S2*", "S2"), ("G", "G*"), ("G*", "G")]:
                w.pop(i+1)
                w.pop(i)
                changed = True
                break
            # Orthogonality
            elif pair in [("S1*", "S2"), ("S2*", "S1")]:
                return "0"
            # Commutativity of G with Cuntz
            elif pair[0] == "G" and pair[1] in ["S1", "S2", "S1*", "S2*"]:
                w[i], w[i+1] = w[i+1], w[i]
                changed = True
                break
            elif pair[0] == "G*" and pair[1] in ["S1", "S2", "S1*", "S2*"]:
                w[i], w[i+1] = w[i+1], w[i]
                changed = True
                break
    return w

def simplify_expr(expr_dict):
    """
    expr_dict maps a tuple of strings (a word) to its coefficient.
    Returns a simplified expr_dict.
    """
    new_expr = {}
    for word, coeff in expr_dict.items():
        if coeff == 0: continue
        w = list(word)
        res = reduce_word(w)
        if res == "0": continue
        w = tuple(res)
        
        # Apply completeness: S2 S2* = 1 - S1 S1*
        # We search for ("S2", "S2*") in w and expand it.
        # This can happen multiple times.
        def expand_completeness(word_tuple, current_coeff):
            for i in range(len(word_tuple)-1):
                if word_tuple[i] == "S2" and word_tuple[i+1] == "S2*":
                    # Replaced with 1
                    w1 = word_tuple[:i] + word_tuple[i+2:]
                    # Replaced with -S1 S1*
                    w2 = word_tuple[:i] + ("S1", "S1*") + word_tuple[i+2:]
                    # Recursively expand
                    expand_completeness(w1, current_coeff)
                    expand_completeness(w2, -current_coeff)
                    return
            
            # If no S2 S2* found, add to new_expr
            w_reduced = tuple(reduce_word(list(word_tuple)))
            if w_reduced != tuple("0"):
                new_expr[w_reduced] = new_expr.get(w_reduced, 0) + current_coeff
                
        expand_completeness(w, coeff)
        
    # Clean up zeros
    return {k: v for k, v in new_expr.items() if v != 0}

def mul(e1, e2):
    res = {}
    for w1, c1 in e1.items():
        for w2, c2 in e2.items():
            w = w1 + w2
            res[w] = res.get(w, 0) + c1 * c2
    return simplify_expr(res)

def add(e1, e2):
    res = dict(e1)
    for w, c in e2.items():
        res[w] = res.get(w, 0) + c
    return simplify_expr(res)

def fmt(e):
    if not e: return "0"
    terms = []
    for w, c in e.items():
        word_str = " ".join(w) if w else "1"
        if c == 1: terms.append(word_str)
        elif c == -1: terms.append("-" + word_str)
        else: terms.append(f"{c} {word_str}")
    return " + ".join(terms)

print("--- Paperwall SUSY Superalgebra Witness ---\n")

# 1. Verify Cuntz Fermionization
c = {("S2", "S1*"): 1}
c_star = {("S1", "S2*"): 1}

print("§1. Cuntz Algebra Canonical Fermion")
c_sq = mul(c, c)
print(f"   c^2 = {fmt(c_sq)}  (Nilpotent/Pauli exclusion)  ✓")

anti_comm = add(mul(c, c_star), mul(c_star, c))
print(f"   {{c, c†}} = {fmt(anti_comm)}  (Canonical Fermion Anticommutator)  ✓")
assert fmt(c_sq) == "0"
assert fmt(anti_comm) == "1"


# 2. Paperwall SUSY Supercharge
print("\n§2. Paperwall SUSY Construction via Chiral Glide Reflections")
# The supercharge couples the Cuntz fermion to the geometric glide reflection
# Q = c * G
G_op = {("G",): 1}
G_star_op = {("G*",): 1}

Q = mul(c, G_op)
Q_star = mul(G_star_op, c_star)

Q_sq = mul(Q, Q)
print(f"   Q^2 = {fmt(Q_sq)}  (Supercharge nilpotency)  ✓")
assert fmt(Q_sq) == "0"

# The SUSY Hamiltonian H = {Q, Q†}
H_susy = add(mul(Q, Q_star), mul(Q_star, Q))
print(f"   H = {{Q, Q†}} = {fmt(H_susy)}  (Topological flat-band Hamiltonian)  ✓")
assert fmt(H_susy) == "1"

print("\nPaperwall Holography Superalgebra formally verified.")
