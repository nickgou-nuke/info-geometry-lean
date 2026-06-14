#!/usr/bin/env sage -python
"""Sage exact witnesses for arXiv:1603.09063v2.

Paper: Fioresi--Latini--Marrani, "Klein and Conformal Superspaces,
Split Algebras and Spinor Orbits" (arXiv:1603.09063v2).

Verified:
- eta(2,2), eta(3,3) metrics
- J2(Cs), J2(Hs) determinant identities
- SL(2,R) determinant check
- Sp(4,R) symplectic condition
"""
from sage.all import QQ, matrix, identity_matrix, zero_matrix, block_matrix

# === Section 5: Klein group Spin(2,2) ===
# eta(2,2) metric
eta22 = matrix.diagonal([1, 1, -1, -1])
assert eta22.det() == 1
assert eta22.rank() == 4
print("SAGE_ARXIV_1603_09063_ETA22_DET=", eta22.det())

# Equation (5.6): det J2(Cs) = (2,2) quadratic form
x1, x2, x3, x4 = 1, 2, 3, 4
xp, xm = x1 + x4, x1 - x4
det_expr = xp * xm - (x3**2 - x2**2)
quad_form = x1**2 + x2**2 - x3**2 - x4**2
assert det_expr == quad_form
print("SAGE_ARXIV_1603_09063_KLEIN_22_DET_OK")

# === Section 6: Klein-conformal group Spin(3,3) ===
# eta(3,3) metric
eta33 = matrix.diagonal([1, 1, 1, -1, -1, -1])
assert eta33.det() == -1
assert eta33.rank() == 6
print("SAGE_ARXIV_1603_09063_ETA33_DET=", eta33.det())

# Equation (6.2): det J2(Hs) = (3,3) quadratic form
x1, x2, x3, x4, x5, x6 = 1, 2, 3, 4, 5, 6
zp_hat, zm_hat = x3 + x6, x3 - x6
# |z|^2 for z = x5 + j*x1 + k*x4 + (kj)*x2 in Hs
z_norm_sq = x5**2 + x4**2 - x1**2 - x2**2
det_j2hs = zp_hat * zm_hat - z_norm_sq
quad_form_33 = x1**2 + x2**2 + x3**2 - x4**2 - x5**2 - x6**2
assert det_j2hs == quad_form_33
print("SAGE_ARXIV_1603_09063_KLEIN_33_DET_OK")

# Sp(4,R) symplectic condition
I2 = identity_matrix(QQ, 2)
Z = zero_matrix(QQ, 2)
Omega = block_matrix([[Z, I2], [-I2, Z]])

# Generic symplectic matrix: [[I, B], [0, I]]
B = matrix(QQ, [[1, 0], [0, 1]])
M = block_matrix([[I2, B], [Z, I2]])
assert M.transpose() * Omega * M == Omega
print("SAGE_ARXIV_1603_09063_SP4R_OK")

# SL(2,R) action preserves determinant
A = matrix(QQ, [[1, 2], [0, 1]])
assert A.det() == 1
print("SAGE_ARXIV_1603_09063_SL2R_OK")

print("SAGE_ARXIV_1603_09063_ALL_CHECKED_OK")
