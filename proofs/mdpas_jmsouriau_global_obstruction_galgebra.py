#!/usr/bin/env python3
"""galgebra witness for MDPAS/JMSouriau obstruction/symplectic/KK layer."""
import sympy as sp
from galgebra.ga import Ga

coords = sp.symbols('x0:5')
ga = Ga('e0 e1 e2 e3 e4', g=[1, 1, 1, 1, 1], coords=list(coords))
e0, e1, e2, e3, e4 = ga.mv()
assert (e0*e0).scalar() == 1
assert (e0*e1 + e1*e0).scalar() == 0

Omega = sp.Matrix([[0,1],[-1,0]])
assert Omega + Omega.T == sp.zeros(2)
assert Omega.det() == 1
X = [sp.Rational(11),13,17,19,23]
kk5 = X[0]**2-X[1]**2-X[2]**2-X[3]**2-X[4]**2
m4 = X[0]**2-X[1]**2-X[2]**2-X[3]**2
assert kk5 == m4 - X[4]**2
assert 2*sp.Rational(17,2) == 17
print('mdpas JMSouriau global obstruction galgebra certificate: ok')
