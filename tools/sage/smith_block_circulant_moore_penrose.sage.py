#!/usr/bin/env sage -python
"""Sage exact-rational certificate for Smith 1977 block-circulant MP inverse."""

from __future__ import annotations

from sage.all import Matrix, QQ, identity_matrix


def assert_zero_matrix(mat, label: str) -> None:
    if mat != Matrix(QQ, mat.nrows(), mat.ncols(), 0):
        raise AssertionError(f"{label} failed:\n{mat}")


def main() -> None:
    print("=== Smith 1977 block-circulant Moore-Penrose Sage certificate ===")
    q = Matrix(
        QQ,
        [
            [0, 0, 1, 0, 0, 0],
            [0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, 1],
            [1, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0],
        ],
    )
    a = Matrix(
        QQ,
        [
            [1, 0, 1, 0, 0, 0],
            [0, 2, 0, 0, 0, 1],
            [0, 0, 1, 0, 1, 0],
            [0, 1, 0, 2, 0, 0],
            [1, 0, 0, 0, 1, 0],
            [0, 0, 0, 1, 0, 2],
        ],
    )
    ap = Matrix(
        QQ,
        [
            [QQ(1) / 2, 0, -QQ(1) / 2, 0, QQ(1) / 2, 0],
            [0, QQ(4) / 9, 0, QQ(1) / 9, 0, -QQ(2) / 9],
            [QQ(1) / 2, 0, QQ(1) / 2, 0, -QQ(1) / 2, 0],
            [0, -QQ(2) / 9, 0, QQ(4) / 9, 0, QQ(1) / 9],
            [-QQ(1) / 2, 0, QQ(1) / 2, 0, QQ(1) / 2, 0],
            [0, QQ(1) / 9, 0, -QQ(2) / 9, 0, QQ(4) / 9],
        ],
    )
    i6 = identity_matrix(QQ, 6)

    assert a.det() == QQ(18)
    assert_zero_matrix(a * q - q * a, "A block-circulant shift commutator")
    assert_zero_matrix(ap * q - q * ap, "A+ block-circulant shift commutator")
    assert ap == a.inverse()
    assert a * ap == i6
    assert ap * a == i6
    assert a * ap * a == a
    assert ap * a * ap == ap
    assert (a * ap).transpose() == a * ap
    assert (ap * a).transpose() == ap * a

    print("PASS: exact QQ determinant, inverse, shift commutation, and MP laws")
    print("SMITH1977_BLOCK_CIRCULANT_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
