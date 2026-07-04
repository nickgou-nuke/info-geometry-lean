#!/usr/bin/env sage -python
"""Sage exact-polynomial verifier for Zorn determinant ratio / scalar-flow identities."""
from sage.all import PolynomialRing, QQ

R = PolynomialRing(QQ, 'a,b,u1,u2,u3,v1,v2,v3,c,d,x1,x2,x3,y1,y2,y3,r,s,t')
a,b,u1,u2,u3,v1,v2,v3,c,d,x1,x2,x3,y1,y2,y3,r,s,t = R.gens()


def dot(u, v):
    return sum(u[i] * v[i] for i in range(3))


def norm(Z):
    A, U, V, B = Z
    return A * B - dot(U, V)


def scale(lam, Z):
    A, U, V, B = Z
    return (lam*A, [lam*z for z in U], [lam*z for z in V], lam*B)


def components(Z):
    A, U, V, B = Z
    return [A] + U + V + [B]


def assert_zero(name, value):
    if value != 0:
        raise AssertionError(f"{name} failed: {value}")
    print(f"PASS: {name}")

X = (a, [u1,u2,u3], [v1,v2,v3], b)
Y = (c, [x1,x2,x3], [y1,y2,y3], d)
NX = norm(X)
NY = norm(Y)

for lhs, rhs in zip(components(scale(s, scale(t, X))), components(scale(s*t, X))):
    assert_zero("scalar flow composes component", lhs - rhs)
assert_zero("N(scale_r(X)) = r^2 N(X)", norm(scale(r, X)) - r**2 * NX)
assert_zero("N(scale_r(Y)) = r^2 N(Y)", norm(scale(r, Y)) - r**2 * NY)
assert_zero("common-scaling determinant ratio invariant", norm(scale(r, Y))*NX - NY*norm(scale(r, X)))
assert_zero("unequal-scaling determinant ratio factor", s**2*norm(scale(t, Y))*NX - t**2*NY*norm(scale(s, X)))
print("ZORN_DETERMINANT_RATIO_FLOW_SCALING_OK")
