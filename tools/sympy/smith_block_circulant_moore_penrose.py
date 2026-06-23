#!/usr/bin/env python3
"""Exact-rational SymPy certificate for Smith 1977 block circulants.

Smith proves that a block `k`-circulant matrix with `|k| = 1` has a
Moore-Penrose inverse in the same block `k`-circulant class.  This certificate
checks a nontrivial rational `3`-block, `2 x 2`-block circulant witness:

* `A` commutes with the cyclic block shift `Q ⊗ I_2`;
* the displayed rational matrix is exactly `A^{-1}`;
* the displayed inverse also commutes with `Q ⊗ I_2`;
* the four Moore-Penrose equations hold over `QQ`.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    if mat != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{mat}")


def matrix_data() -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    q = sp.Matrix(
        [
            [0, 0, 1, 0, 0, 0],
            [0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, 1],
            [1, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0],
        ]
    )
    a = sp.Matrix(
        [
            [1, 0, 1, 0, 0, 0],
            [0, 2, 0, 0, 0, 1],
            [0, 0, 1, 0, 1, 0],
            [0, 1, 0, 2, 0, 0],
            [1, 0, 0, 0, 1, 0],
            [0, 0, 0, 1, 0, 2],
        ]
    )
    ap = sp.Matrix(
        [
            [sp.Rational(1, 2), 0, sp.Rational(-1, 2), 0, sp.Rational(1, 2), 0],
            [0, sp.Rational(4, 9), 0, sp.Rational(1, 9), 0, sp.Rational(-2, 9)],
            [sp.Rational(1, 2), 0, sp.Rational(1, 2), 0, sp.Rational(-1, 2), 0],
            [0, sp.Rational(-2, 9), 0, sp.Rational(4, 9), 0, sp.Rational(1, 9)],
            [sp.Rational(-1, 2), 0, sp.Rational(1, 2), 0, sp.Rational(1, 2), 0],
            [0, sp.Rational(1, 9), 0, sp.Rational(-2, 9), 0, sp.Rational(4, 9)],
        ]
    )
    return q, a, ap


def main() -> None:
    print("=== Smith 1977 block-circulant Moore-Penrose SymPy certificate ===")
    q, a, ap = matrix_data()
    eye = sp.eye(6)

    assert a.det() == 18
    assert_zero_matrix(a * q - q * a, "A block-circulant shift commutator")
    assert_zero_matrix(ap * q - q * ap, "A+ block-circulant shift commutator")
    assert_zero_matrix(ap - a.inv(), "displayed inverse")
    assert_zero_matrix(a * ap - eye, "right inverse")
    assert_zero_matrix(ap * a - eye, "left inverse")

    assert_zero_matrix(a * ap * a - a, "Penrose A A+ A = A")
    assert_zero_matrix(ap * a * ap - ap, "Penrose A+ A A+ = A+")
    assert_zero_matrix((a * ap).T - a * ap, "Penrose A A+ symmetric")
    assert_zero_matrix((ap * a).T - ap * a, "Penrose A+ A symmetric")

    print("PASS: det(A)=18, shift commutation, exact inverse, and MP laws")
    print("SMITH1977_BLOCK_CIRCULANT_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
