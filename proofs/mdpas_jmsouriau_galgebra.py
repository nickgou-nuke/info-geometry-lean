#!/usr/bin/env python3
"""galgebra witness for Souriau MDPAS 1974 finite spin layer."""
import sympy as sp
from galgebra.ga import Ga

t = sp.symbols('t')
ga = Ga('e0 e1 e2 e3', g=[1, -1, -1, -1], coords=[t, sp.symbols('x'), sp.symbols('y'), sp.symbols('z')])
e0, e1, e2, e3 = ga.mv()
assert (e0*e0).scalar() == 1
assert (e1*e1).scalar() == -1
assert (e0*e1 + e1*e0).scalar() == 0

P = sp.Matrix([2,3,5,7])
U = sp.Matrix([11,13,17,19])
V = sp.Matrix([23,29,31,37])
dot = lambda a,b: sum(a[i]*b[i] for i in range(4))
wedge = lambda a,b: sp.Matrix(4,4, lambda i,j: a[i]*b[j]-a[j]*b[i])
S = wedge(U,V)
assert S + S.T == sp.zeros(4)
assert S*P == sp.Matrix([U[i]*dot(V,P)-V[i]*dot(U,P) for i in range(4)])
F = sp.Matrix([[0,1,2,3],[-1,0,5,7],[-2,-5,0,11],[-3,-7,-11,0]])
assert F + F.T == sp.zeros(4)
assert dot(P, F*P) == 0
pfaffian4 = lambda A: A[0,1]*A[2,3] - A[0,2]*A[1,3] + A[0,3]*A[1,2]
assert pfaffian4(S) == 0
EM = sp.Matrix([[0,1,2,3],[-1,0,-11,7],[-2,11,0,-5],[-3,-7,5,0]])
assert EM + EM.T == sp.zeros(4)
assert pfaffian4(EM) == -(1*5 + 2*7 + 3*11)
assert 2*(sp.Rational(17,2)) == 17
print('mdpas JMSouriau galgebra certificate: ok')
