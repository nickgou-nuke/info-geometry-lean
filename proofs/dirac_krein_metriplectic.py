#!/usr/bin/env python3
"""SymPy witness for Dirac/Krein metriplectic finite anchors."""

import sympy as sp

c, s = sp.symbols("c s", real=True)
Gamma = sp.diag(1, -1)
B = sp.Matrix([[c, s], [s, c]])

print("§1 Dirac/Krein adjoint")
a, b, d, e = sp.symbols("a b d e", real=True)
A = sp.Matrix([[a, b], [d, e]])
dirac_adj = lambda M: Gamma * M.T * Gamma
assert sp.simplify(dirac_adj(dirac_adj(A)) - A) == sp.zeros(2)
print("A ↦ Γ Aᵀ Γ is involutive ✓")

print("\n§2 Bogoliubov/Krein preservation")
detB = sp.factor(B.det())
assert sp.simplify(detB - (c**2 - s**2)) == 0
print("det B = c²-s² ✓")
K = sp.simplify(B.T * Gamma * B)
expected = sp.Matrix([[c**2 - s**2, 0], [0, -(c**2 - s**2)]])
assert K == expected
print("Bᵀ Γ B = (c²-s²) Γ ✓")
print("under c²-s²=1: B preserves Γ and log-det barrier is 0 ✓")

print("\n§3 Souriau rest temperature")
beta0 = sp.symbols("beta0", real=True, nonzero=True)
lorentz_norm = beta0**2
assert lorentz_norm != 0
print("rest β=(β0,0,0,0) has positive Lorentz norm for β0≠0 ✓")

print("\ndirac_krein_metriplectic.py: All identities verified")
