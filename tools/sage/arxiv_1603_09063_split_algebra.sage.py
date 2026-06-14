#!/usr/bin/env sage -python
"""Sage exact quadratic-form witnesses for arXiv:1603.09063v2.

Scope: determinant/signature checks for equations (5.6) and (6.2) only.
No global Spin/conformal/symplectic/orbit theorem is claimed here.
"""
from sage.all import QQ, matrix, PolynomialRing

R = PolynomialRing(QQ, names=("x1", "x2", "x3", "x4", "x5", "x6"))
x1, x2, x3, x4, x5, x6 = R.gens()

eta22 = matrix(QQ, [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]])
assert eta22.det() == 1
assert eta22.rank() == 4

# Paper equation (5.6): det [[x+,a],[abar,x-]] = x1^2+x2^2-x3^2-x4^2.
det_22 = (x1 + x4) * (x1 - x4) - (x3**2 - x2**2)
quad_22 = x1**2 + x2**2 - x3**2 - x4**2
assert det_22 == quad_22

eta33 = matrix(QQ, 6, 6, lambda i, j: 0)
for i in range(3):
    eta33[i, i] = 1
for i in range(3, 6):
    eta33[i, i] = -1
assert eta33.det() == -1
assert eta33.rank() == 6

# Paper equation (6.2): z=x5+jx1+kx4+(kj)x2, |z|^2=x5^2+x4^2-x1^2-x2^2.
z_norm_sq = x5**2 + x4**2 - x1**2 - x2**2
det_33 = (x3 + x6) * (x3 - x6) - z_norm_sq
quad_33 = x1**2 + x2**2 + x3**2 - x4**2 - x5**2 - x6**2
assert det_33 == quad_33

print("SAGE_ARXIV_1603_09063_ETA22_DET=", eta22.det())
print("SAGE_ARXIV_1603_09063_ETA22_SIGNATURE=2,2")
print("SAGE_ARXIV_1603_09063_KLEIN_22_DET_OK")
print("SAGE_ARXIV_1603_09063_ETA33_DET=", eta33.det())
print("SAGE_ARXIV_1603_09063_ETA33_SIGNATURE=3,3")
print("SAGE_ARXIV_1603_09063_KLEIN_33_DET_OK")
