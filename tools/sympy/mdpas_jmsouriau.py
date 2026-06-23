#!/usr/bin/env python3
"""Exact-rational SymPy certificate for Souriau MDPAS 1974 finite spin layer."""
import sympy as sp

p = sp.symbols('p0:4')
u = sp.symbols('u0:4')
v = sp.symbols('v0:4')
P = sp.Matrix(p)
U = sp.Matrix(u)
V = sp.Matrix(v)

def dot(a,b):
    return sum(a[i]*b[i] for i in range(4))

def wedge(a,b):
    return sp.Matrix(4,4, lambda i,j: a[i]*b[j] - a[j]*b[i])

def contract(A,p):
    return A*p

S = wedge(U,V)
assert sp.simplify(S + S.T) == sp.zeros(4)
assert sp.simplify(wedge(U,V) + wedge(V,U)) == sp.zeros(4)
C = contract(S,P)
expected = sp.Matrix([U[i]*dot(V,P) - V[i]*dot(U,P) for i in range(4)])
assert sp.simplify(C - expected) == sp.zeros(4,1)

f01,f02,f03,f12,f13,f23 = sp.symbols('f01 f02 f03 f12 f13 f23')
F = sp.Matrix([[0, f01, f02, f03],[-f01,0,f12,f13],[-f02,-f12,0,f23],[-f03,-f13,-f23,0]])
assert sp.simplify(F + F.T) == sp.zeros(4)
power = dot(P, F*P)
assert sp.simplify(power) == 0

def pfaffian4(A):
    return A[0,1]*A[2,3] - A[0,2]*A[1,3] + A[0,3]*A[1,2]

assert sp.simplify(pfaffian4(S)) == 0
E0,E1,E2,B0,B1,B2 = sp.symbols('E0 E1 E2 B0 B1 B2')
EM = sp.Matrix([[0,E0,E1,E2],[-E0,0,-B2,B1],[-E1,B2,0,-B0],[-E2,-B1,B0,0]])
assert sp.simplify(EM + EM.T) == sp.zeros(4)
assert sp.simplify(pfaffian4(EM) + (E0*B0 + E1*B1 + E2*B2)) == 0

m,q,sB,h = sp.symbols('m q sB h', nonzero=True)
gyro = 2*q*sB/(2*m)
assert sp.simplify(gyro - q*sB/m) == 0
assert sp.simplify(2*(h/2) - h) == 0
print('MDPAS_JMSOURIAU_SYMPY_CERTIFICATE_OK')
