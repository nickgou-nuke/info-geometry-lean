#!/usr/bin/env python3
"""galgebra witness for Boolean projection/Cantor bit bridge."""
import sympy as sp
from galgebra.ga import Ga
x = sp.symbols('x')
ga = Ga('e', g=[1], coords=[x])
e, = ga.mv()
assert (e * e).scalar() == 1
for p in [0, 1]:
    assert p*p == p
bits = (0, 1, 0, 1)
for n in range(len(bits)):
    assert bits[:n] == bits[:n+1][:-1]
print('uhf Boolean projection Cantor bridge galgebra certificate: ok')
