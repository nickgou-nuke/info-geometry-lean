"""Assertion verifier for the finite Majorana braid-group certificate.

Mirrors `MajoranaBraidGroup.lean`: real 8x8 integer Majorana atoms, their
bivectors, unnormalised braid generators 1 + gamma_i gamma_{i+1}, the adjacent
Artin relation, and projective inverse numerators.
"""

import sympy as sp


def kron(*matrices):
    out = matrices[0]
    for matrix in matrices[1:]:
        out = sp.kronecker_product(out, matrix)
    return out


I2 = sp.eye(2)
X = sp.Matrix([[0, 1], [1, 0]])
Z = sp.Matrix([[1, 0], [0, -1]])
J = sp.Matrix([[0, 1], [-1, 0]])

I8 = sp.eye(8)
Z8 = sp.zeros(8)

gamma1 = kron(X, I2, I2)
gamma2 = kron(Z, I2, I2)
gamma3 = kron(J, J, I2)

for i, gamma in enumerate([gamma1, gamma2, gamma3], start=1):
    assert gamma * gamma == I8, f"gamma{i} square failed"

pairs = [(1, gamma1, 2, gamma2), (2, gamma2, 3, gamma3), (1, gamma1, 3, gamma3)]
for i, a, j, b in pairs:
    assert a * b + b * a == Z8, f"gamma{i}, gamma{j} anticomm failed"

bivector12 = gamma1 * gamma2
bivector23 = gamma2 * gamma3
assert bivector12 * bivector12 == -I8
assert bivector23 * bivector23 == -I8

braid12 = I8 + bivector12
braid23 = I8 + bivector23
assert braid12 * braid23 * braid12 == braid23 * braid12 * braid23

assert braid12 * (I8 - bivector12) == 2 * I8
assert braid23 * (I8 - bivector23) == 2 * I8

print("OK finite Majorana braid-group certificate")
