#!/usr/bin/env python3
"""clifford exact-rational witness for Barbaresco SPIGL 2020 finite Souriau layer."""
import sympy as sp
from clifford import Cl

layout, blades = Cl(2, 0, firstIdx=1)
e1, e2 = blades['e1'], blades['e2']
assert e1 * e1 == layout.scalar
assert e2 * e2 == layout.scalar
assert e1 * e2 + e2 * e1 == 0

X = sp.Matrix([[1, 2], [3, 5]])
Y = sp.Matrix([[7, 11], [13, 17]])
Z = sp.Matrix([[19, 23], [29, 31]])
F = sp.Matrix([[37, 41], [43, 47]])
comm = lambda A, B: A*B - B*A
kks = lambda A, B: sp.trace(F * comm(A, B))
assert comm(X, X) == sp.zeros(2)
assert comm(X, Y) + comm(Y, X) == sp.zeros(2)
assert comm(X, comm(Y, Z)) + comm(Y, comm(Z, X)) + comm(Z, comm(X, Y)) == sp.zeros(2)
assert kks(X, X) == 0
assert kks(X, Y) + kks(Y, X) == 0
assert kks(X, comm(Y, Z)) + kks(Y, comm(Z, X)) + kks(Z, comm(X, Y)) == 0
print('barbaresco SPIGL2020 clifford certificate: ok')
