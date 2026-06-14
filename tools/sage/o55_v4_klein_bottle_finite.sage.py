#!/usr/bin/env sage -python
"""Sage exact witnesses for finite O(5,5)/V4/Klein-bottle shadows."""

from sage.all import QQ, matrix, identity_matrix, PolynomialRing, vector

R = PolynomialRing(QQ, [f"x{i}" for i in range(10)] + [f"y{i}" for i in range(10)] + ["a"])
gens = R.gens()
x = vector(R, gens[:10])
y = vector(R, gens[10:20])
a = gens[20]


def pair(u, v):
    return sum(u[i] * v[i + 5] + u[i + 5] * v[i] for i in range(5))


def diag_with_flips(*idx):
    m = identity_matrix(R, 10)
    for i in idx:
        m[i, i] = -1
    return m


def trans0(v, amount):
    w = vector(R, v)
    w[0] += amount
    return w


def aff_refl0(v):
    w = vector(R, v)
    w[0] = -w[0]
    return w

I = identity_matrix(R, 10)
neg = -I
r0 = diag_with_flips(0, 5)
r1 = diag_with_flips(1, 6)

for name, m in [("neg", neg), ("r0", r0), ("r1", r1), ("r0r1", r0 * r1)]:
    assert pair(m * x, m * y) == pair(x, y), name
    assert m * m == I, name

assert r0 * r1 == r1 * r0
assert aff_refl0(trans0(aff_refl0(x), a)) == trans0(x, -a)

print("SAGE_O55_V4_NEG_PAIRING_OK")
print("SAGE_O55_V4_REFLECTIONS_OK")
print("SAGE_O55_V4_COMMUTING_INVOLUTIONS_OK")
print("SAGE_O55_KLEIN_BOTTLE_AFFINE_RELATION_OK")
