#!/usr/bin/env sage -python
"""Sage exact witnesses for theorem-safe Jordan--Cayley inversion identities.

Lean owner: lean/InfoGeometry/Algebra/JordanCayleyInversion.lean
Scope: finite rational coordinate identities only.
"""
from sage.all import QQ, PolynomialRing

R = PolynomialRing(QQ, names=("A", "B", "C", "u", "v", "xp", "xm", "ar", "ai", "r"))
A, B, C, u, v, xp, xm, ar, ai, r = R.gens()

# Planar inversion line-to-circle numerator.
den = u**2 + v**2
pulled_num = den * (A * (u / den) + B * ((-v) / den) + C)
circle_num = C * (u**2 + v**2) + A * u - B * v
assert pulled_num.numerator() == circle_num
assert pulled_num.denominator() == 1

# Split-complex arithmetic over QQ-polynomials.
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def neg(x): return (-x[0], -x[1])
def mul(x, y): return (x[0]*y[0] + x[1]*y[1], x[0]*y[1] + x[1]*y[0])
def scalar(t): return (t, R(0))
def norm(x): return x[0]**2 - x[1]**2

def scale(t, X):
    xp0, xm0, a0 = X
    return (t*xp0, t*xm0, mul(scalar(t), a0))

def trrev(X):
    xp0, xm0, a0 = X
    return (xm0, xp0, neg(a0))

def det(X):
    xp0, xm0, a0 = X
    return xp0*xm0 - norm(a0)

X = (xp, xm, (ar, ai))
assert trrev(trrev(X)) == X
assert det(trrev(X)) == det(X)
assert det(scale(r, X)) == r**2 * det(X)

# Cayley determinant and involution as rational-function identities.
d = det(X)
W = scale(1/d, trrev(X))
assert det(W) == 1/d
assert scale(1/det(W), trrev(W)) == X

print("SAGE_JORDAN_CAYLEY_PLANAR_LINE_TO_CIRCLE_OK")
print("SAGE_JORDAN_CAYLEY_CS_TRREV_INVOLUTIVE_OK")
print("SAGE_JORDAN_CAYLEY_CS_DET_TRREV_OK")
print("SAGE_JORDAN_CAYLEY_CS_DET_SCALE_OK")
print("SAGE_JORDAN_CAYLEY_CS_DET_INVERSION_OK")
print("SAGE_JORDAN_CAYLEY_CS_INVERSION_INVOLUTIVE_OK")
