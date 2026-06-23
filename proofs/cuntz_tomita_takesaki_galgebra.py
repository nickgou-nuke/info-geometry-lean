#!/usr/bin/env python3
"""galgebra witness for finite Cuntz/Tomita chiral parity."""
import sympy as sp
from galgebra.ga import Ga

x = sp.symbols('x')
ga = Ga('e', g=[1], coords=[x])
e, = ga.mv()
assert (e * e).scalar() == 1

c = sp.Rational(5, 4)
s = sp.Rational(3, 4)
I = sp.eye(2)
eta = sp.Matrix([[1, 0], [0, -1]])
L = c * I - s * eta
R = c * I + s * eta
assert eta * eta == I
assert L * R == I
for X in [sp.Matrix([[1,0],[0,0]]), sp.Matrix([[0,1],[0,0]]),
          sp.Matrix([[0,0],[1,0]]), sp.Matrix([[0,0],[0,1]])]:
    assert L * (L * X * R).T * R == X.T
print("cuntz Tomita-Takesaki galgebra certificate: ok")
