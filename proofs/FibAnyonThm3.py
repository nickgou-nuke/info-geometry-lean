#!/usr/bin/env python3
"""SymPy witness for FibAnyonThm3: R-matrix for Fibonacci anyons."""
import sympy as sp

R1 = sp.exp(-4*sp.pi*sp.I/5)
Rτ = sp.exp(3*sp.pi*sp.I/5)
Rdet = sp.exp(-sp.pi*sp.I/5)
R = sp.diag(R1, Rτ)

print("═══ R-matrix verification ═══")
det_ok = sp.simplify(R.det() / Rdet) == 1
uni_ok = sp.simplify(R * R.T.conjugate()) == sp.eye(2)
print(f"  R = diag(e^{-4*sp.pi*sp.I/5}, e^{3*sp.pi*sp.I/5})")
print(f"  det(R) = e^{-sp.pi*sp.I/5}: {det_ok}")
print(f"  R·R† = I: {uni_ok}")
print(f"\n✅ R-matrix verified." if det_ok and uni_ok else "\n❌ R-matrix verification failed.")
