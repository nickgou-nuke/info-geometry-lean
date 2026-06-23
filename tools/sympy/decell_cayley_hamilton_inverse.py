#!/usr/bin/env python3
"""Exact rational audit for Decell's Cayley-Hamilton generalized inverse.

The paper proves that, for a complex matrix A and B = A A*, the Moore-Penrose
inverse can be computed from the nonzero coefficient tail of the characteristic
polynomial of B.  This script checks the formula over rational matrices and
then verifies the four Penrose equations directly.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{simplified}")


def decell_inverse(A: sp.Matrix) -> sp.Matrix:
    """Compute Decell's formula using B = A A.T over exact rationals."""
    B = A * A.T
    n = B.rows
    coeffs = [sp.simplify(c) for c in B.charpoly().all_coeffs()]

    k = max(i for i, coeff in enumerate(coeffs) if coeff != 0)
    if k == 0:
        return sp.zeros(A.cols, A.rows)

    tail = sp.zeros(n, n)
    for j in range(k):
        tail += coeffs[j] * (B ** (k - 1 - j))

    return sp.simplify((-sp.Rational(1, 1) / coeffs[k]) * A.T * tail)


def check_penrose(A: sp.Matrix, A_plus: sp.Matrix, label: str) -> None:
    """Verify the four Moore-Penrose equations for real rational matrices."""
    assert_zero_matrix(A * A_plus * A - A, f"{label}: A A+ A = A")
    assert_zero_matrix(A_plus * A * A_plus - A_plus, f"{label}: A+ A A+ = A+")
    assert_zero_matrix((A * A_plus).T - A * A_plus, f"{label}: A A+ symmetric")
    assert_zero_matrix((A_plus * A).T - A_plus * A, f"{label}: A+ A symmetric")


def run_case(A: sp.Matrix, label: str) -> None:
    A_plus = decell_inverse(A)
    check_penrose(A, A_plus, label)

    library_pinv = A.pinv()
    assert_zero_matrix(A_plus - library_pinv, f"{label}: Decell formula equals SymPy pinv")

    B = A * A.T
    coeffs = [sp.factor(c) for c in B.charpoly().all_coeffs()]
    print(f"[ok] {label}")
    print(f"     A = {A.tolist()}")
    print(f"     charpoly(AA^T) coefficients = {coeffs}")
    print(f"     A+ = {A_plus.tolist()}")


def main() -> None:
    run_case(sp.Matrix([[1, 2, 3], [2, 4, 6]]), "rank-one rectangular 2x3")
    run_case(sp.Matrix([[1, 2], [3, 5]]), "invertible square 2x2")
    run_case(sp.Matrix([[1, 0, 1], [0, 1, 1], [1, 1, 2]]), "rank-two symmetric 3x3")
    run_case(sp.zeros(2, 3), "zero rectangular 2x3")


if __name__ == "__main__":
    main()
