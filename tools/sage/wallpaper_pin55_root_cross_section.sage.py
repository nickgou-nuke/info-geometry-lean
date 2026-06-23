#!/usr/bin/env sage
# Exact-rational Sage certificate for the wallpaper/Pin(5,5) root cross-section.

from sage.all import QQ, diagonal_matrix, identity_matrix, matrix, zero_matrix
from itertools import permutations, product


def mat_key(M):
    return tuple(M.list())


def vec_key(v):
    return tuple(v.list())


print("=== Wallpaper / Pin(5,5) root cross-section Sage certificate ===")

I2 = identity_matrix(QQ, 2)
I5 = identity_matrix(QQ, 5)
T = matrix(QQ, [[0, -1], [1, 0]])
G = diagonal_matrix(QQ, [1, -1])
D4 = [I2, T, -I2, -T, G, T * G, -G, -T * G]
D4set = {mat_key(S) for S in D4}

signed_perm_2 = []
for perm in permutations(range(2)):
    for signs in product([QQ(1), QQ(-1)], repeat=2):
        M = zero_matrix(QQ, 2, 2)
        for col, row in enumerate(perm):
            M[row, col] = signs[col]
        signed_perm_2.append(M)
compatible = [
    S for S in signed_perm_2
    if S.transpose() * S == I2 and (S * T == T * S or S * T == -T * S)
]
assert {mat_key(S) for S in compatible} == D4set
assert len(D4set) == 8

b2_roots = [
    matrix(QQ, 2, 1, [1, 0]),
    matrix(QQ, 2, 1, [-1, 0]),
    matrix(QQ, 2, 1, [0, 1]),
    matrix(QQ, 2, 1, [0, -1]),
    matrix(QQ, 2, 1, [1, 1]),
    matrix(QQ, 2, 1, [-1, -1]),
    matrix(QQ, 2, 1, [1, -1]),
    matrix(QQ, 2, 1, [-1, 1]),
]
b2set = {vec_key(r) for r in b2_roots}
for S in D4:
    for r in b2_roots:
        assert vec_key(S * r) in b2set

d5_roots = []
for i in range(5):
    for j in range(i + 1, 5):
        for si in [QQ(1), QQ(-1)]:
            for sj in [QQ(1), QQ(-1)]:
                r = zero_matrix(QQ, 5, 1)
                r[i, 0] = si
                r[j, 0] = sj
                d5_roots.extend([r, -r])
d5set = {vec_key(r) for r in d5_roots}
assert len(d5set) == 40
projected = {vec_key(matrix(QQ, 2, 1, [r[0, 0], r[1, 0]])) for r in d5_roots}
assert b2set == {p for p in projected if p != (QQ(0), QQ(0))}

lifts = [
    matrix(QQ, 5, 1, [1, 0, 1, 0, 0]),
    matrix(QQ, 5, 1, [-1, 0, 1, 0, 0]),
    matrix(QQ, 5, 1, [0, 1, 1, 0, 0]),
    matrix(QQ, 5, 1, [0, -1, 1, 0, 0]),
    matrix(QQ, 5, 1, [1, 1, 0, 0, 0]),
    matrix(QQ, 5, 1, [-1, -1, 0, 0, 0]),
    matrix(QQ, 5, 1, [1, -1, 0, 0, 0]),
    matrix(QQ, 5, 1, [-1, 1, 0, 0, 0]),
]
for lift, root in zip(lifts, b2_roots):
    assert vec_key(lift) in d5set
    assert matrix(QQ, 2, 1, [lift[0, 0], lift[1, 0]]) == root

cross = [
    I5,
    matrix(QQ, [[0, -1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    diagonal_matrix(QQ, [-1, -1, 1, 1, 1]),
    matrix(QQ, [[0, 1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    diagonal_matrix(QQ, [1, -1, -1, 1, 1]),
    matrix(QQ, [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    diagonal_matrix(QQ, [-1, 1, -1, 1, 1]),
    matrix(QQ, [[0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
]
eta55 = diagonal_matrix(QQ, [1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
for P, S in zip(cross, D4):
    assert P.transpose() * P == I5
    assert P.submatrix(0, 0, 2, 2) == S
    assert all(vec_key(P * r) in d5set for r in d5_roots)
    L = P.block_sum(P)
    assert L.transpose() * eta55 * L == eta55

print("WALLPAPER_PIN55_ROOT_CROSS_SECTION_SAGE_CERTIFICATE_OK")
