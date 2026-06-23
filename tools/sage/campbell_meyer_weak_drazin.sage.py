#!/usr/bin/env sage -python
"""
Exact Sage certificate for Campbell--Meyer 1978 weak Drazin inverses.
All arithmetic is over QQ.
"""

from __future__ import annotations

from sage.all import Matrix, QQ, identity_matrix, zero_matrix


def assert_zero_matrix(m, label: str) -> None:
    if m != zero_matrix(QQ, m.nrows(), m.ncols()):
        raise AssertionError(f"{label} failed:\n{m}")


def assert_weak(a, b, k: int, label: str) -> None:
    assert_zero_matrix(b * (a ** (k + 1)) - (a ** k), f"{label}: B A^(k+1) = A^k")


def assert_drazin(a, d, k: int, label: str) -> None:
    assert_zero_matrix(a * d - d * a, f"{label}: A D = D A")
    assert_zero_matrix(d * a * d - d, f"{label}: D A D = D")
    assert_zero_matrix((a ** (k + 1)) * d - (a ** k), f"{label}: A^(k+1)D = A^k")


def main() -> None:
    print("=== Campbell--Meyer 1978 weak Drazin Sage certificate ===")

    a = Matrix(QQ, [[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    nil = Matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    ident = identity_matrix(QQ, 3)
    assert nil**2 == zero_matrix(QQ, 3, 3)
    assert a**2 == Matrix(QQ, [[4, 0, 0], [0, 0, 0], [0, 0, 0]])
    assert a**3 == 2 * (a**2)

    drazin = Matrix(QQ, [[QQ(1) / 2, 0, 0], [0, 0, 0], [0, 0, 0]])
    assert_drazin(a, drazin, 2, "Drazin inverse")
    assert_weak(a, drazin, 2, "Drazin inverse")

    wild = Matrix(QQ, [[QQ(1) / 2, 3, 5], [0, 7, 11], [0, 13, 17]])
    assert_weak(a, wild, 2, "wild weak inverse")
    assert wild != drazin
    assert a * wild != wild * a

    polynomial = (QQ(1) / 2) * ident
    assert_weak(a, polynomial, 2, "polynomial weak inverse")
    assert a * polynomial == polynomial * a
    assert polynomial.det() == QQ(1) / 8
    p1 = (a * ident).trace()
    assert p1 == 2
    assert (QQ(1) / p1) * ident == polynomial
    assert polynomial != drazin

    projective = Matrix(QQ, [[QQ(1) / 2, 2, 3], [0, 0, 5], [0, 0, 7]])
    assert_weak(a, projective, 2, "projective-shaped weak inverse")
    ba = projective * a
    assert ba == Matrix(QQ, [[1, 0, 2], [0, 0, 0], [0, 0, 0]])
    assert ba**2 == ba

    commuting = Matrix(QQ, [[QQ(1) / 2, 0, 0], [0, 3, 4], [0, 0, 3]])
    assert_weak(a, commuting, 2, "commuting weak inverse")
    assert a * commuting == commuting * a

    p = Matrix(QQ, [[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    assert p * p == ident
    assert_weak(p * a * p, p * polynomial * p, 2, "GL_3(Q) conjugate")

    print("CAMPBELL_MEYER_WEAK_DRAZIN_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
