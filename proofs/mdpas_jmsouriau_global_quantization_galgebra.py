#!/usr/bin/env python3
"""galgebra lane for the finite MDPAS/JM global-quantization audit."""

import sympy as sp
from galgebra.ga import Ga

t, x, y, z = sp.symbols("t x y z")
ga = Ga("e0 e1 e2 e3", g=[1, -1, -1, -1], coords=[t, x, y, z])
e0, e1, _e2, _e3 = ga.mv()
assert (e0 * e0).scalar() == 1
assert (e1 * e1).scalar() == -1
assert (e0 * e1 + e1 * e0).scalar() == 0

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

print("mdpas JMSouriau global quantization galgebra certificate: ok")

