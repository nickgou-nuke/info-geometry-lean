#!/usr/bin/env sage
"""Exact-rational Sage audit for the finite holographic Cuntz shard."""

from sage.all import Matrix, QQ, identity_matrix, vector


def main() -> None:
    print("=== Holographic Cuntz shard Sage audit ===")

    S = Matrix(QQ, [[0, 1], [0, 0]])
    T = Matrix(QQ, [[0, 0], [1, 0]])
    p = Matrix(QQ, [[0, 0], [0, 1]])
    q = Matrix(QQ, [[1, 0], [0, 0]])
    I2 = identity_matrix(QQ, 2)
    x = vector(QQ, [3, 5])

    assert S.transpose() * S == p
    assert S * S.transpose() == q
    assert T.transpose() * T == q
    assert S.transpose() * (S * x) == p * x
    assert p * p == p
    assert q * q == q
    assert p + q == I2
    assert q != I2
    assert S * S.transpose() * S == S
    print("HOLOGRAPHIC_CUNTZ_SHARD_SAGE_AUDIT_OK")


main()
