#!/usr/bin/env sage -python
from sage.all import Matrix, QQ, identity_matrix, zero_matrix

print('=== CUNTZ HOLOGRAM SHARD SAGE CERTIFICATE ===')

S_left = Matrix(QQ, [[1,0],[0,1],[0,0],[0,0]])
S_right = Matrix(QQ, [[0,0],[0,0],[1,0],[0,1]])
I2 = identity_matrix(QQ, 2)
I4 = identity_matrix(QQ, 4)

assert S_left.transpose() * S_left == I2
assert S_right.transpose() * S_right == I2
assert S_left.transpose() * S_right == zero_matrix(QQ, 2, 2)
assert S_right.transpose() * S_left == zero_matrix(QQ, 2, 2)
print('PASS: branch isometries and orthogonality')

P_left = S_left * S_left.transpose()
P_right = S_right * S_right.transpose()
assert P_left + P_right == I4
print('PASS: branch range projections sum to identity')

print('CUNTZ_HOLOGRAM_SHARD_SAGE_OK')
