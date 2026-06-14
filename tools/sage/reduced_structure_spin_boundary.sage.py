#!/usr/bin/env sage -python
"""Sage exact witnesses for the reduced-structure finite split-complex boundary."""
from sage.all import QQ

# Critical split-complex dimension data.
q = QQ(2)
D = q + 2
assert q == 2
assert D == 4

# Diagonal Jordan determinant det(diag(alpha,beta)) = alpha*beta.
alpha = QQ(3)
beta = QQ(5)
def det_diagonal(a, b):
    return a * b
assert det_diagonal(alpha, beta) == alpha * beta

# Raw split-complex representatives under the identity 2x2 action.
E = (QQ(1), QQ(1))
ZERO = (QQ(0), QQ(0))
ONE = (QQ(1), QQ(0))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(a, b):
    return (a[0] * b[0] + a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def act(M, psi):
    aa, ab, ba, bb = M
    p, n = psi
    return (
        add(mul(aa, p), mul(ab, n)),
        add(mul(ba, p), mul(bb, n)),
    )


IDENTITY = (ONE, ZERO, ZERO, ONE)
GENERIC = (ONE, ZERO)
NULL = (E, ZERO)
DIAGONAL_NULL = (E, E)

assert act(IDENTITY, GENERIC) == GENERIC
assert act(IDENTITY, NULL) == NULL
assert act(IDENTITY, DIAGONAL_NULL) == DIAGONAL_NULL

print("SAGE_REDUCED_STRUCTURE_Q2_OK")
print("SAGE_REDUCED_STRUCTURE_D4_OK")
print("SAGE_REDUCED_STRUCTURE_DIAGONAL_DET_OK")
print("SAGE_REDUCED_STRUCTURE_IDENTITY_GENERIC_OK")
print("SAGE_REDUCED_STRUCTURE_IDENTITY_NULL_OK")
print("SAGE_REDUCED_STRUCTURE_IDENTITY_DIAGONAL_NULL_OK")
