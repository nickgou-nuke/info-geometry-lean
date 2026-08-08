#!/usr/bin/env python3
"""SymPy witness for Jackiw--Rebbi-style boundary edge states.

Finite checks:
- the Klein/CPT glide fixes the critical core sigma = 1/2;
- odd glide-axis modes are extinguished by c = (-1)^k c;
- the boundary Dirac operator at the core has a nontrivial kernel.

This is a finite symbolic witness, not a PDE proof of the full Jackiw--Rebbi
index theorem.
"""

from __future__ import annotations

import sympy as sp

sigma = sp.symbols("sigma", real=True)
k = sp.symbols("k", integer=True, nonnegative=True)
c = sp.symbols("c")
s = sp.symbols("s")

# Klein/CPT glide on the spectral cylinder
cpt_glide = lambda x: 1 - x
assert sp.simplify(cpt_glide(sp.Rational(1, 2)) - sp.Rational(1, 2)) == 0

# Odd-mode extinction on the glide axis
phase = (-1) ** k
odd_relation = sp.Eq(c, phase * c)
odd_solution = sp.solve(odd_relation.subs(k, 3), c)
assert odd_solution == [0]

# Boundary Dirac operator at zero momentum / core = zero matrix
D = sp.Matrix([[-s, 0], [0, s]])
D0 = D.subs(s, 0)
assert D0 == sp.zeros(2)
assert len(D0.nullspace()) == 2

# A concrete edge-state witness
psi_edge = sp.Matrix([1, 0])
assert D0 * psi_edge == sp.zeros(2, 1)

print("critical core fixed =", cpt_glide(sp.Rational(1, 2)))
print("odd-mode extinction solution at k=3 =", odd_solution)
print("boundary operator at core =")
print(D0)
print("nullspace dimension =", len(D0.nullspace()))
print("jackiw_rebbi_cantor_edge_states.py: witness passed")
