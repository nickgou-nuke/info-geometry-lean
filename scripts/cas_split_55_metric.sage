#!/usr/bin/env sage
"""Exact Sage certificate for the split (5,5) metric and Witt basis."""

K.<s> = QuadraticField(2)
I5 = identity_matrix(QQ, 5)
eta = diagonal_matrix(QQ, [1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
Q = block_matrix(QQ, [[zero_matrix(QQ, 5), I5], [I5, zero_matrix(QQ, 5)]])
U = (1/s) * block_matrix(K, [[I5, I5], [I5, -I5]])
etaK = matrix(K, eta)
QK = matrix(K, Q)

assert eta.is_symmetric()
assert Q.is_symmetric()
assert eta.rank() == 10
assert Q.rank() == 10
assert eta.eigenvalues().count(1) == 5
assert eta.eigenvalues().count(-1) == 5
assert Q.eigenvalues().count(1) == 5
assert Q.eigenvalues().count(-1) == 5
assert U.transpose() * etaK * U == QK

print("SPLIT_55_METRIC_EVIDENCE")
print("carrier_dimension=10")
print("diagonal_signature=(5,5)")
print("witt_form=[[0,I5],[I5,0]]")
print("witt_signature=(5,5)")
print("witt_transform=verified")
print("STATUS=PASS")

