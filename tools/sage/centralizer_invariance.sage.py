#!/usr/bin/env sage -python
"""Sage exact witness for central-sign conjugation."""

from sage.all import Matrix, QQ, identity_matrix

M = Matrix(QQ, [[2, 3], [5, 7]])
I2 = identity_matrix(QQ, 2)
neg = -I2

assert neg * M * neg == M
assert I2 * M * I2 == M

print("SAGE_CENTRALIZER_NEG_ONE_CONJUGATION_OK")
print("SAGE_CENTRALIZER_SIGN_FRAME_OK")
