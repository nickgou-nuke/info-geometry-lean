#!/usr/bin/env sage
# Exact-rational Sage certificate for the split-octonion projective null boundary.

from sage.all import *

P = matrix(QQ, [[1, 0], [0, 0]])
M = matrix(QQ, [[0, 0], [0, 1]])
I2 = identity_matrix(QQ, 2)

assert P * P == P
assert M * M == M
assert P * M == zero_matrix(QQ, 2, 2)
assert M * P == zero_matrix(QQ, 2, 2)
assert P + M == I2
assert P.det() == 0
assert M.det() == 0

def zorn_norm(a, b, u, v):
    return a * b - sum(ui * vi for ui, vi in zip(u, v))

assert zorn_norm(QQ(1), QQ(0), (QQ(0), QQ(0), QQ(0)), (QQ(0), QQ(0), QQ(0))) == 0
assert zorn_norm(QQ(0), QQ(1), (QQ(0), QQ(0), QQ(0)), (QQ(0), QQ(0), QQ(0))) == 0

print("split-octonion projective null boundary Sage certificate: ok")
