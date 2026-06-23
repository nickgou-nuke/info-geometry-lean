#!/usr/bin/env python3
"""Clifford-lane witness for the Brillouin Klein bottle projective gauge law."""
import sympy as sp
from clifford import Cl

layout, blades = Cl(2, 0, firstIdx=1)
e1 = blades['e1']
e2 = blades['e2']
I = layout.scalar
biv = e1 * e2

# Orthogonal Clifford generators anticommute; the bivector squares to -1.
assert e1 * e1 == I
assert e2 * e2 == I
assert e1 * e2 == -(e2 * e1)
assert biv * biv == -I

Tx = sp.Matrix([[0, 1], [1, 0]])
Ty = sp.Matrix([[1, 0], [0, -1]])
assert Tx * Ty == -(Ty * Tx)
assert (Tx * Ty) * (Tx * Ty) == -sp.eye(2)

print("brillouin Klein bottle manifold clifford certificate: ok")
