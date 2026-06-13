#!/usr/bin/env sage -python
"""Sage exact finite witness for the Clifford central-core packet."""

from sage.all import Matrix, ZZ, identity_matrix, CyclotomicField

M = MatrixSpace = None
Mat = Matrix(ZZ, [[1, 0], [0, 1]]).parent()
I2 = identity_matrix(ZZ, 2)
J = Matrix(ZZ, [[0, 1], [-1, 0]])
E = Matrix(ZZ, [[1, 0], [0, -1]])
P = E * J

assert J * J == -I2
assert J * (-J) == I2 and (-J) * J == I2
assert E * E == I2
assert E * J + J * E == Matrix(ZZ, [[0, 0], [0, 0]])
assert P * P == I2
assert J * I2 * (-J) == I2
assert J * (-I2) * (-J) == -I2

K = CyclotomicField(4)
z = K.gen()
assert z**2 == -1

print("SAGE_CLIFFORD_BRAIDING_CENTER_OK")
