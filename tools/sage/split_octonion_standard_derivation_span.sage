#!/usr/bin/env sage
"""Exact span audit for standard derivations of the real split octonions.

This is a discovery/audit lane only.  Lean remains the proof authority.  The
coordinate order and parameter readout exactly match
`CanonicalZornDerivationDimension.lean`:

    E11, E22, U0, U1, U2, V0, V1, V2.
"""

from itertools import combinations
from sage.all import QQ, matrix, vector

NAMES = ("E11", "E22", "U0", "U1", "U2", "V0", "V1", "V2")
BASIS = tuple(vector(QQ, [1 if i == j else 0 for i in range(8)]) for j in range(8))


def cross(x, y):
    return vector(QQ, [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ])


def dot(x, y):
    return sum(x[i] * y[i] for i in range(3))


def mul(X, Y):
    """Canonical/vector Zorn product used by Lean."""
    a, b = X[0], X[1]
    c, d = Y[0], Y[1]
    v, w = vector(QQ, X[2:5]), vector(QQ, X[5:8])
    x, y = vector(QQ, Y[2:5]), vector(QQ, Y[5:8])
    return vector(QQ, [
        a * c + dot(v, y),
        dot(w, x) + b * d,
        *(a * x + d * v - cross(w, y)),
        *(c * w + b * y + cross(v, x)),
    ])


def standard_derivation(a, b, z):
    """D_ab = [L_a,L_b] + [L_a,R_b] + [R_a,R_b]."""
    return (
        mul(a, mul(b, z)) - mul(b, mul(a, z))
        + mul(a, mul(z, b)) - mul(mul(a, z), b)
        + mul(mul(z, b), a) - mul(mul(z, a), b)
    )


def parameter_vector(a, b):
    D = lambda z: standard_derivation(a, b, z)
    E22, U0, U1 = BASIS[1], BASIS[2], BASIS[3]
    V0, V1, V2 = BASIS[5], BASIS[6], BASIS[7]
    return vector(QQ, [
        D(E22)[5], D(V1)[5], D(V2)[5],
        D(E22)[6], D(U0)[6], D(V0)[6], D(V1)[6], D(V2)[6],
        D(E22)[7], D(U0)[7], D(U1)[7], D(V0)[7], D(V1)[7], D(V2)[7],
    ])


pairs = list(combinations(range(8), 2))
columns = [parameter_vector(BASIS[i], BASIS[j]) for i, j in pairs]
full = matrix(QQ, 14, len(columns), lambda r, c: columns[c][r])

selected = []
rank = 0
for column_index in range(len(columns)):
    trial = matrix(QQ, 14, len(selected) + 1,
                   lambda r, c: columns[(selected + [column_index])[c]][r])
    if trial.rank() > rank:
        selected.append(column_index)
        rank += 1
    if rank == 14:
        break

minor = matrix(QQ, 14, 14,
               lambda r, c: columns[selected[c]][r])

print(f"all-pairs rank: {full.rank()}")
print(f"selected minor determinant: {minor.det()}")
print("selected pairs and Lean parameter columns:")
for k, column_index in enumerate(selected):
    i, j = pairs[column_index]
    print(f"  {k:2d}: D_{{{NAMES[i]},{NAMES[j]}}}  {list(columns[column_index])}")

assert full.rank() == 14
assert minor.det() != 0
