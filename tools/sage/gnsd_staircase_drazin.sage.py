#!/usr/bin/env sage -python
"""
Sage exact certificate for GNSD staircase and Drazin block algebra.

Run with:

  DOT_SAGE=/tmp/sage-dot-sage /home/goutev/miniforge3/envs/sage/bin/python \
    tools/sage/gnsd_staircase_drazin.sage.py
"""

from sage.all import Matrix, QQ, block_diagonal_matrix, block_matrix, identity_matrix, zero_matrix


def jordan_zero(k: int):
    return Matrix(QQ, k, k, lambda i, j: QQ(1) if j == i + 1 else QQ(0))


def nullity(a):
    return a.ncols() - a.rank()


def main() -> None:
    print("=== Sage GNSD staircase / Drazin certificate ===")

    sizes = [3, 2, 1]
    a = block_diagonal_matrix([jordan_zero(k) for k in sizes])
    nullities = [nullity(a**j) for j in range(0, 4)]
    mu = [nullities[j] - nullities[j - 1] for j in range(1, 4)]
    assert nullities == [0, 3, 5, 6]
    assert mu == [3, 2, 1]
    print("PASS: nullity increments recover GNSD diagonal sizes")

    n = Matrix(QQ, [[0, 1], [0, 0]])
    m = Matrix(QQ, [[2, 1], [0, 3]])
    mi = m.inverse()
    k = Matrix(QQ, [[1, 2], [-1, 1]])
    ell = k * m - n * k

    z = zero_matrix(QQ, 2)
    i2 = identity_matrix(QQ, 2)
    b = block_matrix(QQ, [[n, ell], [z, m]])
    shear = block_matrix(QQ, [[i2, k], [z, i2]])
    shear_inv = block_matrix(QQ, [[i2, -k], [z, i2]])
    diag_nm = block_matrix(QQ, [[n, z], [z, m]])
    assert shear_inv * b * shear == diag_nm
    print("PASS: Sylvester shear decouples the upper coupling")

    d = block_matrix(QQ, [[z, k * mi], [z, mi]])
    assert d * b * d == d
    assert b * d == d * b
    assert b**3 * d == b**2
    print("PASS: Drazin block formula satisfies the index-2 laws")

    print("GNSD_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
