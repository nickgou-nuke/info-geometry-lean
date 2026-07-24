#!/usr/bin/env sage
"""
Explicit construction of Lie algebra g2 and an 8-dimensional stabilizer
subalgebra acting on split octonions over QQ. The real form of the stabilizer
is not identified from dimension alone.
"""

from sage.all import *
import json

print("="*70)
print("Lie Algebra g2 and Stabilizer Subalgebra on Split Octonions")
print("="*70)

O = OctonionAlgebra(QQ, -1, -1, 1)
basis = O.basis()
n = len(basis)

# Get structure constants
c = {}
for i in range(n):
    for k in range(n):
        prod = basis[i] * basis[k]
        for r in range(n):
            c[(i, k, r)] = prod.coefficient(r)

# Derivation equations system
rows = []
for i in range(n):
    for k in range(n):
        for s in range(n):
            row = [0] * (n*n)
            for r in range(n):
                row[s*n + r] += c[(i, k, r)]
            for j in range(n):
                row[j*n + i] -= c[(j, k, s)]
            for j in range(n):
                row[j*n + k] -= c[(i, j, s)]
            rows.append(row)

# g2 derivations Lie algebra
A_g2 = Matrix(QQ, rows)
K_g2 = A_g2.right_kernel()
basis_g2 = K_g2.basis()
gens_g2 = [matrix(QQ, 8, 8, b.list()) for b in basis_g2]

print(f"✓ Derivation algebra g2 dimension: {len(gens_g2)}")

# Stabilizer derivations preserving J = basis[1] (e1)
rows_stabilizer = list(rows)
for s in range(n):
    row = [0] * (n*n)
    row[s*n + 1] = 1
    rows_stabilizer.append(row)
A_stabilizer = Matrix(QQ, rows_stabilizer)
K_stabilizer = A_stabilizer.right_kernel()
basis_stabilizer = K_stabilizer.basis()
gens_stabilizer = [matrix(QQ, 8, 8, b.list()) for b in basis_stabilizer]

print(f"✓ Stabilizer algebra dimension: {len(gens_stabilizer)}")

# Lie bracket closure helper
def verify_closure(gens, K):
    for X in gens:
        for Y in gens:
            bracket = X * Y - Y * X
            bracket_flat = vector(QQ, bracket.list())
            if bracket_flat not in K:
                return False
    return True

g2_closed = verify_closure(gens_g2, K_g2)
stabilizer_closed = verify_closure(gens_stabilizer, K_stabilizer)

print(f"  g2 Lie algebra closed: {g2_closed}")
print(f"  stabilizer Lie algebra closed: {stabilizer_closed}")

# Export generators
export_data = {
    "g2_dimension": len(gens_g2),
    "stabilizer_dimension": len(gens_stabilizer),
    "g2_generators": [[[str(val) for val in row] for row in X.rows()] for X in gens_g2],
    "stabilizer_generators": [[[str(val) for val in row] for row in X.rows()] for X in gens_stabilizer],
    "g2_closed": bool(g2_closed),
    "stabilizer_closed": bool(stabilizer_closed)
}

with open("/tmp/g2_stabilizer_generators.json", "w") as f:
    json.dump(export_data, f, indent=2)

print("\n✓ Concrete generators exported to /tmp/g2_stabilizer_generators.json")
print("="*70)
