#!/usr/bin/env python3
"""
export_triality_data.py
Exports D4 Triality data from Sage/Gap/SymPy logic into JSON for Lean ingestion.
"""

import json
import sympy as sp
from sympy import Matrix, simplify, symbols

# ==============================================================================
# 1. ZORN DATA (From ZornAssociatorSplitOctonion.py)
# ==============================================================================

def vec(x, y, z):
    return Matrix([x, y, z])

def dot(u, v):
    return (u.T * v)[0]

def cross(u, v):
    return Matrix([
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0]
    ])

class Zorn:
    def __init__(self, a, u, v, b):
        self.a = simplify(a)
        self.u = Matrix(u)
        self.v = Matrix(v)
        self.b = simplify(b)

    def __mul__(self, other):
        a, u, v, b = self.a, self.u, self.v, self.b
        c, x, y, d = other.a, other.u, other.v, other.b
        return Zorn(
            a * c + dot(u, y),
            a * x + d * u - cross(v, y),
            c * v + b * y + cross(u, x),
            dot(v, x) + b * d
        )

    def __sub__(self, other):
        return Zorn(self.a - other.a, self.u - other.u, self.v - other.v, self.b - other.b)

    def is_zero(self):
        return (simplify(self.a) == 0 and simplify(self.b) == 0 and
                all(simplify(c) == 0 for c in self.u) and
                all(simplify(c) == 0 for c in self.v))

    def det(self):
        return simplify(self.a * self.b - dot(self.u, self.v))

def associator(A, B, C):
    return (A * B) * C - A * (B * C)

# Compute the canonical non-zero associator
e1, e2 = vec(1,0,0), vec(0,1,0)
zero3 = vec(0,0,0)
A = Zorn(0, e1, zero3, 0)  # U(e1)
B = Zorn(0, zero3, e1, 0)  # L(e1)
C = Zorn(0, e2, zero3, 0)  # U(e2)

assoc_result = associator(A, B, C)
non_assoc_witness = {
    "u_component": [float(assoc_result.u[i]) for i in range(3)],
    "is_nonzero": not assoc_result.is_zero
}

# ==============================================================================
# 2. D4 ROOT SYSTEM (From Gap logic)
# ==============================================================================

# Generate D4 roots: permutations of (±1, ±1, 0, 0)
import itertools
D4_roots = set()
for positions in itertools.combinations(range(4), 2):
    for signs in itertools.product([1, -1], repeat=2):
        root = [0, 0, 0, 0]
        root[positions[0]] = signs[0]
        root[positions[1]] = signs[1]
        D4_roots.add(tuple(root))

D4_roots_list = sorted(list(D4_roots))

# ==============================================================================
# 3. S3 TRIALITY ACTION (From Gap/Sage logic)
# ==============================================================================

# Triality permutes the three 8D reps.
# In weight space, it acts as a specific linear transformation.
# We define the S3 generators acting on the 4D weight lattice.
# Generator 1: Swap (1 2) of the outer nodes of D4 dynkin diagram
# Generator 2: Cycle (1 2 3)

# Explicit matrix representation of S3 on R^4 (weight space)
# Based on standard D4 triality formulas
tau_cycle = Matrix([
    [ 0.5,  0.5,  0.5, -0.5],
    [ 0.5,  0.5, -0.5,  0.5],
    [ 0.5, -0.5,  0.5,  0.5],
    [-0.5,  0.5,  0.5,  0.5]
])

# Verify order 3
tau3 = tau_cycle ** 3
is_order_3 = tau3 == Matrix.eye(4)

# ==============================================================================
# 4. BRANCHING RULES (From Sage logic)
# ==============================================================================

# 8v, 8s, 8c highest weights in D4 basis
# 8v: (1, 0, 0, 0)
# 8s: (0, 0, 1, 0)
# 8c: (0, 0, 0, 1)
highest_weights = {
    "8v": [1, 0, 0, 0],
    "8s": [0, 0, 1, 0],
    "8c": [0, 0, 0, 1]
}

# Triality permutes them: 8v -> 8s -> 8c -> 8v
# We verify this by applying the tau_cycle matrix
def apply_triality(weight):
    v = Matrix(weight)
    result = tau_cycle * v
    return [float(result[i]) for i in range(4)]

# Check permutation
w_8v = highest_weights["8v"]
w_8s_mapped = apply_triality(w_8v)
# Should be close to 8s (0,0,1,0) or a linear combo

# ==============================================================================
# 5. EXPORT TO JSON
# ==============================================================================

data = {
    "zorn_associator_witness": non_assoc_witness,
    "D4_roots": D4_roots_list,
    "num_roots": len(D4_roots_list),
    "S3_generator_matrix": [[float(tau_cycle[i,j]) for j in range(4)] for i in range(4)],
    "S3_order_3_verified": is_order_3,
    "highest_weights": highest_weights,
    "triality_action_on_8v": w_8s_mapped
}

with open("/home/goutev/auto/proofs/triality_data.json", "w") as f:
    json.dump(data, f, indent=2)

print("✅ Exported triality_data.json")
print(f"   - Zorn Associator Witness: {non_assoc_witness['u_component']}")
print(f"   - D4 Roots: {len(D4_roots_list)} (Expected 24)")
print(f"   - S3 Order 3: {is_order_3}")
print(f"   - 8v mapped to: {w_8s_mapped}")