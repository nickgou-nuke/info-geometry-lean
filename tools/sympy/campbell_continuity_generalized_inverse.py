#!/usr/bin/env python3
"""Exact rational audit for Campbell 1977 continuity decompositions."""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{simplified}")


def one_norm(mat: sp.Matrix) -> sp.Rational:
    if mat.rows == 0 or mat.cols == 0:
        return sp.Rational(0)
    return max(sum(abs(sp.simplify(mat[i, j])) for i in range(mat.rows)) for j in range(mat.cols))


def decell_inverse(A: sp.Matrix) -> sp.Matrix:
    B = A * A.T
    coeffs = [sp.simplify(c) for c in B.charpoly().all_coeffs()]
    k = max(i for i, coeff in enumerate(coeffs) if coeff != 0)
    if k == 0:
        return sp.zeros(A.cols, A.rows)
    tail = sp.zeros(B.rows, B.cols)
    for j in range(k):
        tail += coeffs[j] * (B ** (k - 1 - j))
    return sp.simplify((-sp.Rational(1) / coeffs[k]) * A.T * tail)


def moore_penrose_audit() -> None:
    A = sp.Matrix([[1, 2, 3], [2, 4, 6]])
    Ap = decell_inverse(A)
    F = sp.Matrix([[sp.Rational(1, 100), 0], [sp.Rational(-1, 150), sp.Rational(1, 90)], [0, sp.Rational(1, 120)]])
    X = Ap + F
    I_m = sp.eye(A.rows)
    I_n = sp.eye(A.cols)

    E1 = A * X * A - A
    E2 = X * A * X - X
    E3 = A * X - X.T * A.T
    E4 = X * A - A.T * X.T

    rhs = (
        Ap * E1 * Ap
        + (I_n - Ap * A) * E4 * Ap
        + Ap * E3 * (I_m - A * Ap)
        + (I_n - Ap * A) * (-E2 + E4 * Ap * E3) * (I_m - A * Ap)
    )
    assert_zero_matrix(F - rhs, "Campbell Moore-Penrose residual decomposition")

    bound = (
        one_norm(E1) * one_norm(Ap) ** 2
        + one_norm(E2) * one_norm(Ap * A) * one_norm(I_m - A * Ap)
        + one_norm(E4) * one_norm(I_n - Ap * A) * one_norm(Ap)
        + (one_norm(E2) + one_norm(E4) * one_norm(Ap) * one_norm(E3))
        * one_norm(I_n - Ap * A)
        * one_norm(I_m - A * Ap)
    )
    assert one_norm(F) <= sp.simplify(bound)
    print("PASS: Moore-Penrose residual decomposition and 1-norm bound")


def group_inverse_audit() -> None:
    A = sp.diag(1, 0)
    Ag = A
    F = sp.Matrix([[sp.Rational(1, 50), sp.Rational(1, 80)], [sp.Rational(-1, 70), sp.Rational(1, 60)]])
    X = Ag + F
    I = sp.eye(2)
    P = Ag * A

    E1 = X * A * X - X
    E2 = X * A - A * X
    E3 = A ** 2 * X - A

    rhs = (
        Ag * Ag * E3 * P
        + -Ag * E2 * (I - P)
        + (I - P) * E2 * Ag
        + (I - P) * (-E2 * Ag * E2 - E1) * (I - P)
    )
    assert_zero_matrix(F - rhs, "Campbell group-inverse residual decomposition")

    bound = (
        one_norm(Ag) ** 2 * one_norm(E3)
        + one_norm(Ag) * one_norm(E2) * one_norm(I - P)
        + one_norm(I - P) * one_norm(E2) * one_norm(Ag)
        + (one_norm(E1) + one_norm(E2) ** 2 * one_norm(Ag)) * one_norm(I - P) ** 2
    )
    assert one_norm(F) <= sp.simplify(bound)
    print("PASS: group-inverse residual decomposition and 1-norm bound")


def main() -> None:
    moore_penrose_audit()
    group_inverse_audit()
    print("CAMPBELL1977_SYMPY_AUDIT_OK")


if __name__ == "__main__":
    main()
