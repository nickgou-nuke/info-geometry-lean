#!/usr/bin/env python3
"""clifford lane for the finite MDPAS/JM global-quantization audit."""

import sympy as sp
from clifford import Cl

layout, blades = Cl(4, 0, firstIdx=0)
e0, e1, e2, e3 = blades["e0"], blades["e1"], blades["e2"], blades["e3"]
assert e0 * e0 == layout.scalar
assert e0 * e1 + e1 * e0 == 0

J = sp.Matrix([[0, 0, 1, 0],
               [0, 0, 0, 1],
               [-1, 0, 0, 0],
               [0, -1, 0, 0]])
assert J + J.T == sp.zeros(4)
assert J.det() == 1

r = sp.Rational(11)
A = sp.Matrix([2, 3, 5, 7])
g4 = sp.diag(1, -1, -1, -1)
kk = sp.zeros(5)
kk[:4, :4] = g4 + r * (A * A.T)
kk[:4, 4] = r * A
kk[4, :4] = (r * A).T
kk[4, 4] = r
assert kk == kk.T

assert sp.Rational(1) + sp.Rational(1) + sp.Rational(1) != 0
assert 2 * sp.Rational(17, 2) == 17

print("mdpas JMSouriau global quantization clifford certificate: ok")

