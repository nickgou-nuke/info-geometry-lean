#!/usr/bin/env sage
"""Finite Sage witness for Lorentz/biquaternion equivalence.

Closed finite content only:
- Hermitian 2×2 Pauli readout of a spacetime point;
- determinant equals the Minkowski quadratic form;
- exact determinant-one matrix Q preserves the determinant under X ↦ Q X Q;
- the central sign -I acts trivially on this transport lane.
"""

print("=" * 72)
print("SAGE: LORENTZ / BIQUATERNION EQUIVALENCE — FINITE EXACT WITNESS")
print("=" * 72)

R = SR
t, x, y, z = var("t x y z", domain="real")

sigma0 = matrix(R, [[1, 0], [0, 1]])
sigma1 = matrix(R, [[0, 1], [1, 0]])
sigma2 = matrix(R, [[0, -I], [I, 0]])
sigma3 = matrix(R, [[1, 0], [0, -1]])

X = t * sigma0 + x * sigma1 + y * sigma2 + z * sigma3
expected = t^2 - x^2 - y^2 - z^2
assert (X.determinant() - expected).expand() == 0
print("sage: Pauli/Hermitian determinant readout: OK")

Q = matrix(R, [[2, 1], [1, 1]])
assert Q.determinant() == 1
Xp = Q * X * Q
assert (Xp.determinant() - X.determinant()).expand() == 0
print("sage: exact determinant-one transport preserves determinant: OK")

minus_I = -sigma0
assert minus_I * X * minus_I == X
assert ((-Q) * X * (-Q)).determinant().expand() == X.determinant().expand()
print("sage: central sign kernel / sign-changed transport: OK")

print("=" * 72)
print("SAGE LORENTZ / BIQUATERNION FINITE WITNESS VERIFIED")
print("=" * 72)
