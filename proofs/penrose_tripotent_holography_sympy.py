"""SymPy witness: Tripotent Operators and Penrose Holography.

This script formalizes the algebraic shift from standard involutory 
supersymmetry (G^2 = 1) to Tripotent operators (T^3 = T), which 
capture boundary defects with zero-modes (eigenvalues +1, -1, 0).

It also formalizes the golden-ratio inflation symmetry of the 
aperiodic Penrose Cantor-crystal at the holographic boundary, 
using the Cuntz-Krieger adjacency matrix.
"""

import sympy as sp

print("--- Tripotent Operators & Penrose Fractal Symmetries ---\n")

# ══════════════════════════════════════════════════════════════════════════════
# §1. Tripotent Operators (T^3 = T)
# ══════════════════════════════════════════════════════════════════════════════
print("§1. Tripotent Operators and Zero-Modes")
# A generic tripotent operator can have eigenvalues +1, -1, and 0.
# We define a 3x3 tripotent matrix representing a fractional supercharge 
# with a zero-mode (e.g., a non-invertible boundary defect).
T = sp.Matrix([
    [ 1,  0,  0],
    [ 0, -1,  0],
    [ 0,  0,  0]
])

print("  Operator T:")
sp.pprint(T)

T_cube = T * T * T
print("  T^3:")
sp.pprint(T_cube)

print("  Is T tripotent (T^3 == T)?", T_cube == T, "✓")
print("  Spectrum of T:", list(T.eigenvals().keys()), "(Contains the crucial zero-mode!) ✓\n")

# ══════════════════════════════════════════════════════════════════════════════
# §2. Cuntz-Krieger Penrose Boundary (Fractal Inflation)
# ══════════════════════════════════════════════════════════════════════════════
print("§2. Penrose Cantor-Crystal (Cuntz-Krieger Algebra O_A)")
# The Penrose tiling hierarchy (kites and darts) is governed by 
# the Fibonacci inflation rules. Its boundary Cuntz-Krieger algebra 
# is defined by the adjacency matrix A.
A = sp.Matrix([
    [1, 1],
    [1, 0]
])

print("  Penrose Inflation Matrix A:")
sp.pprint(A)

# The scaling dimension of the holographic boundary is determined 
# by the Perron-Frobenius eigenvalue of A.
eigenvals = list(A.eigenvals().keys())
phi = (1 + sp.sqrt(5)) / 2

print("\n  Eigenvalues of A:")
for ev in eigenvals:
    print(f"    {ev}")

# Verify one eigenvalue is exactly the Golden Ratio
match_phi = False
for ev in eigenvals:
    if sp.simplify(ev - phi) == 0:
        match_phi = True

print(f"\n  Does the primary eigenvalue exactly match the Golden Ratio φ = (1+√5)/2? {match_phi} ✓")
print("  This defines the fractal scaling dimension of the Penrose Holoboundary!")
