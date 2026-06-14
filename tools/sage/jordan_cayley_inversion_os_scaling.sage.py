#!/usr/bin/env sage -python
"""Sage exact polynomial witnesses for the concrete `J₂(O_s)` scaling packet."""

from sage.all import QQ, PolynomialRing

R = PolynomialRing(QQ, names=("r", "xp", "xm", "a", "b", "x0", "x1", "x2", "y0", "y1", "y2"))
r, xp, xm, a, b, x0, x1, x2, y0, y1, y2 = R.gens()


def negZ(z):
    return tuple(-c for c in z)


def detZ(z):
    a0, b0, x00, x10, x20, y00, y10, y20 = z
    return a0 * b0 - (x00 * y00 + x10 * y10 + x20 * y20)


def scaleZ(s, z):
    return tuple(s * c for c in z)


def trace_reversal(H):
    xp0, xm0, z0 = H
    return (xm0, xp0, negZ(z0))


def scale(s, H):
    xp0, xm0, z0 = H
    return (s * xp0, s * xm0, scaleZ(s, z0))


def det(H):
    xp0, xm0, z0 = H
    return xp0 * xm0 - detZ(z0)


X = (xp, xm, (a, b, x0, x1, x2, y0, y1, y2))
assert trace_reversal(trace_reversal(X)) == X
assert det(trace_reversal(X)) == det(X)
assert trace_reversal(scale(r, X)) == scale(r, trace_reversal(X))
assert det(scale(r, X)) == r**2 * det(X)

print("SAGE_JORDAN_CAYLEY_OS_TRACE_REVERSAL_INVOLUTIVE_OK")
print("SAGE_JORDAN_CAYLEY_OS_DET_TRACE_REVERSAL_OK")
print("SAGE_JORDAN_CAYLEY_OS_TRACE_REVERSAL_SCALE_OK")
print("SAGE_JORDAN_CAYLEY_OS_DET_SCALE_OK")
