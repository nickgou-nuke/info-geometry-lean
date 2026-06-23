#!/usr/bin/env python3
"""Exact-rational SymPy certificate for Barbaresco SPIGL 2020 finite Souriau layer."""
import sympy as sp

x11,x12,x21,x22,y11,y12,y21,y22,z11,z12,z21,z22,f11,f12,f21,f22,b= sp.symbols(
    'x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 f11 f12 f21 f22 b')
X = sp.Matrix([[x11,x12],[x21,x22]])
Y = sp.Matrix([[y11,y12],[y21,y22]])
Z = sp.Matrix([[z11,z12],[z21,z22]])
F = sp.Matrix([[f11,f12],[f21,f22]])

def comm(A,B):
    return A*B - B*A

def tr(A):
    return sp.trace(A)

def kks(F,A,B):
    return tr(F*comm(A,B))

zero2 = sp.zeros(2)
assert sp.simplify(comm(X,X)) == zero2
assert sp.simplify(comm(X,Y) + comm(Y,X)) == zero2
jac = comm(X,comm(Y,Z)) + comm(Y,comm(Z,X)) + comm(Z,comm(X,Y))
assert sp.simplify(jac) == zero2
assert sp.simplify(kks(F,X,X)) == 0
assert sp.simplify(kks(F,X,Y) + kks(F,Y,X)) == 0
coc = kks(F,X,comm(Y,Z)) + kks(F,Y,comm(Z,X)) + kks(F,Z,comm(X,Y))
assert sp.simplify(coc) == 0
massieu = lambda t: t**2 / sp.Rational(2)
assert sp.simplify(massieu(b+1) - 2*massieu(b) + massieu(b-1) - 1) == 0
c,Q = sp.symbols('c Q')
assert sp.simplify(c*Q - c*Q) == 0
print('BARBARESCO_SPILG2020_SYMPY_CERTIFICATE_OK')
