"""SymPy witness: Spacetime is Spin.

Formalizes the dictionary mapping the emergent 4-vector geometry 
of Special Relativity strictly from the algebraic properties of 
2x2 Hermitian spinor matrices.
"""

import sympy as sp

print("======================================================================")
print("             SPACETIME IS SPIN: THE ALGEBRAIC DICTIONARY              ")
print("======================================================================\n")

# Pauli basis symbols
t, x, y = sp.symbols('t x y', real=True)
z = sp.symbols('z', real=True, positive=True)

# The Hermitian Spacetime Matrix X = t*I + x*sigma_1 + y*sigma_2 + z*sigma_3
X = sp.Matrix([
    [t + z, x - sp.I * y],
    [x + sp.I * y, t - z]
])

print("§1. The Pauli Spacetime Matrix X:")
print(f"{X}\n")

print("§2. The Dictionary of Emergence")

# A. Trace is Time
tr_X = sp.simplify(X.trace())
print(f"  A. Trace = {tr_X}  ->  Time is the invariant scalar expansion.")

# B. Determinant is Metric
det_X = sp.simplify(X.det())
print(f"  B. Determinant = {det_X}  ->  Distance is the algebraic volume.")

# C. Eigenvalues are Lightcone Coordinates
evals = X.eigenvals()
eval_list = list(evals.keys())
print(f"  C. Eigenvalues = {eval_list}")
print("     The eigenvalues (t +/- |r|) represent the null front (lightcone).\n")

print("§3. The Singularity (Lightlike Interval)")
# When the interval is null, det(X) = 0.
# The matrix loses rank and becomes the outer product of a pure spinor.
print("  For a lightlike ray traveling in the z-direction (x=0, y=0, t=z):")
X_null = X.subs({x: 0, y: 0, t: z})
print(f"  X_null =\n{X_null}")

# Spinor factorization
psi = sp.Matrix([[sp.sqrt(2*z)], [0]])
psi_dagger = psi.H
pure_state = psi * psi_dagger

print(f"  Spinor psi =\n{psi}")
print(f"  psi * psi^dagger =\n{pure_state}")

is_pure = sp.simplify(X_null - pure_state) == sp.zeros(2)
print(f"  Matches Pure Spinor State: {is_pure}")

print("\n  Conclusion: Spacetime is not a container for spin;")
print("  Spacetime is a secondary manifestation of spinor algebra. ✓")
