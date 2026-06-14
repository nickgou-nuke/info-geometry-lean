#!/usr/bin/env sage -python
"""Sage exact witness for the finite Pauli B3 braid identity."""

from sage.all import I, Matrix, QQbar, identity_matrix

K = QQbar
one = identity_matrix(K, 2)
s1 = Matrix(K, [[0, 1], [1, 0]])
s2 = Matrix(K, [[0, -I], [I, 0]])
s3 = Matrix(K, [[1, 0], [0, -1]])
A = one + I * s1
B = one + I * s2

assert s1 * s1 == one
assert s2 * s2 == one
assert s3 * s3 == one
assert s1 * s2 == -s2 * s1
assert s1 * s2 == I * s3
assert A * B * A == B * A * B
assert A * B * A == 2 * I * (s1 + s2)

print("SAGE_PAULI_B3_SQUARES_OK")
print("SAGE_PAULI_B3_ANTICOMM_OK")
print("SAGE_PAULI_B3_BRAID_OK")
print("SAGE_PAULI_B3_TRIPLE_PRODUCT_OK")
