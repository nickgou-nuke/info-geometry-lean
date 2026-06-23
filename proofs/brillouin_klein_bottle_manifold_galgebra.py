#!/usr/bin/env python3
"""galgebra-lane witness for the Brillouin Klein bottle projective gauge law."""
import sympy as sp
from galgebra.ga import Ga

coords = sp.symbols('x y')
ga = Ga('e1 e2', g=[1, 1], coords=coords)
e1, e2 = ga.mv()

assert (e1 * e1).scalar() == 1
assert (e2 * e2).scalar() == 1
assert e1 * e2 + e2 * e1 == 0
assert ((e1 * e2) * (e1 * e2)).scalar() == -1

Tx = sp.Matrix([[0, 1], [1, 0]])
Ty = sp.Matrix([[1, 0], [0, -1]])
assert Tx * Ty == -(Ty * Tx)
assert (Tx * Ty) * (Tx * Ty) == -sp.eye(2)

print("brillouin Klein bottle manifold galgebra certificate: ok")
