#!/usr/bin/env python3
"""
Exact symbolic Zorn split-octonion invariant verifier.

Conventions:
  X = [[a, u], [v, b]], with u,v in R^3.
  XY = [[ac + u·y,  a*x + d*u - v×y],
        [c*v + b*y + u×x, v·x + bd]].

This is not associative. It is alternative and satisfies the quadratic
single-element characteristic identity

  X^2 - Tr(X) X + N(X) 1 = 0,

where Tr(X)=a+b and N(X)=ab-u·v.
"""

from __future__ import annotations
import sympy as sp


def dot(x, y):
    return sum(x[i] * y[i] for i in range(3))


def cross(x, y):
    return [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ]


def zadd(X, Y):
    return (X[0] + Y[0],
            [X[1][i] + Y[1][i] for i in range(3)],
            [X[2][i] + Y[2][i] for i in range(3)],
            X[3] + Y[3])


def zneg(X):
    return (-X[0], [-c for c in X[1]], [-c for c in X[2]], -X[3])


def zsub(X, Y):
    return zadd(X, zneg(Y))


def zscale(r, X):
    return (r * X[0], [r * c for c in X[1]], [r * c for c in X[2]], r * X[3])


def zmul(X, Y):
    a, u, v, b = X
    c, x, y, d = Y
    v_cross_y = cross(v, y)
    u_cross_x = cross(u, x)
    return (
        a * c + dot(u, y),
        [a * x[i] + d * u[i] - v_cross_y[i] for i in range(3)],
        [c * v[i] + b * y[i] + u_cross_x[i] for i in range(3)],
        dot(v, x) + b * d,
    )


def ztrace(X):
    return X[0] + X[3]


def znorm(X):
    return X[0] * X[3] - dot(X[1], X[2])


def zconj(X):
    a, u, v, b = X
    return (b, [-c for c in u], [-c for c in v], a)


def zone():
    return (sp.Integer(1), [sp.Integer(0)] * 3, [sp.Integer(0)] * 3, sp.Integer(1))


def zzero():
    return (sp.Integer(0), [sp.Integer(0)] * 3, [sp.Integer(0)] * 3, sp.Integer(0))


def zscalar(r):
    return (r, [sp.Integer(0)] * 3, [sp.Integer(0)] * 3, r)


def associator(X, Y, Z):
    return zsub(zmul(zmul(X, Y), Z), zmul(X, zmul(Y, Z)))


def components(X):
    return [X[0], *X[1], *X[2], X[3]]


def assert_zzero(name, X):
    vals = [sp.expand(c) for c in components(X)]
    if any(v != 0 for v in vals):
        raise AssertionError(f"{name} failed: {vals}")
    print(f"PASS: {name}")


def assert_not_zzero(name, X):
    vals = [sp.expand(c) for c in components(X)]
    if all(v == 0 for v in vals):
        raise AssertionError(f"{name} unexpectedly vanished")
    print(f"PASS: {name}: {vals}")


a, u0, u1, u2, v0, v1, v2, b = sp.symbols("a u0 u1 u2 v0 v1 v2 b")
c, x0, x1, x2, y0, y1, y2, d = sp.symbols("c x0 x1 x2 y0 y1 y2 d")

X = (a, [u0, u1, u2], [v0, v1, v2], b)
Y = (c, [x0, x1, x2], [y0, y1, y2], d)
I = zone()

# conjugation / trace / norm
assert_zzero("X + conjugate(X) = Tr(X) 1",
             zsub(zadd(X, zconj(X)), zscalar(ztrace(X))))
assert_zzero("X conjugate(X) = N(X) 1",
             zsub(zmul(X, zconj(X)), zscalar(znorm(X))))
assert_zzero("conjugate(X) X = N(X) 1",
             zsub(zmul(zconj(X), X), zscalar(znorm(X))))

# quadratic characteristic identity
assert_zzero("quadratic identity X^2 - Tr(X)X + N(X)1 = 0",
             zadd(zsub(zmul(X, X), zscale(ztrace(X), X)), zscalar(znorm(X))))

# alternativity, symbolic in X,Y
assert_zzero("left alternativity (XX)Y = X(XY)", associator(X, X, Y))
assert_zzero("right alternativity (YX)X = Y(XX)", associator(Y, X, X))

# explicit nonassociativity witness: three top-row vector basis elements.
E1 = (0, [1, 0, 0], [0, 0, 0], 0)
E2 = (0, [0, 1, 0], [0, 0, 0], 0)
E3 = (0, [0, 0, 1], [0, 0, 0], 0)
assert_not_zzero("nonassociativity witness (E1,E2,E3)", associator(E1, E2, E3))

# potency boundaries.
P = (1, [1, 0, 0], [0, 0, 0], 0)  # Tr=1, N=0 => P^2=P
assert ztrace(P) == 1 and znorm(P) == 0
assert_zzero("trace-one norm-zero element is idempotent: P^2=P", zsub(zmul(P, P), P))

Q = (0, [1, 0, 0], [0, 0, 0], 0)  # Tr=0, N=0 => Q^2=0
assert ztrace(Q) == 0 and znorm(Q) == 0
assert_zzero("trace-zero norm-zero element is nilpotent: Q^2=0", zmul(Q, Q))

print("All exact SymPy Zorn split-octonion invariant checks passed.")
