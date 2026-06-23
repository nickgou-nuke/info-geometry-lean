#!/usr/bin/env python3
"""
Exact SymPy certificate for Hartwig 1976,
"Singular Value Decomposition and the Moore--Penrose Inverse of Bordered
Matrices".

The packet checks two rational SVD-reduced bordered matrices and their
principal Schur complements.  Star is ordinary transpose because the packet is
real rational.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(entry) != 0 for entry in m):
        raise AssertionError(f"{label} failed:\n{m}")


def assert_mp(a: sp.Matrix, x: sp.Matrix, label: str) -> None:
    assert_zero_matrix(a * x * a - a, f"{label}: A X A = A")
    assert_zero_matrix(x * a * x - x, f"{label}: X A X = X")
    assert_zero_matrix((a * x).T - a * x, f"{label}: (A X)^* = A X")
    assert_zero_matrix((x * a).T - x * a, f"{label}: (X A)^* = X A")


def main() -> None:
    print("=== Hartwig 1976 SVD / Moore--Penrose bordered SymPy certificate ===")

    base_a = sp.diag(sp.Rational(2), sp.Rational(0))
    base_mp = sp.diag(sp.Rational(1, 2), sp.Rational(0))
    assert_mp(base_a, base_mp, "base SVD block")
    print("PASS: SVD-reduced base block has exact Moore--Penrose inverse")

    case1 = sp.Matrix([[2, 0, 3], [0, 0, 0], [1, 0, 5]])
    case1_mp = sp.Matrix(
        [[sp.Rational(5, 7), 0, sp.Rational(-3, 7)],
         [0, 0, 0],
         [sp.Rational(-1, 7), 0, sp.Rational(2, 7)]]
    )
    z = sp.Rational(5) - sp.Rational(1) * sp.Rational(1, 2) * sp.Rational(3)
    assert z == sp.Rational(7, 2)
    assert_mp(case1, case1_mp, "Hartwig Case 1 border")
    schur1 = sp.Matrix([[sp.Rational(7, 5), 0], [0, 0]])
    schur1_mp = sp.Matrix([[sp.Rational(5, 7), 0], [0, 0]])
    assert_mp(schur1, schur1_mp, "Hartwig Case 1 Schur complement")
    print("PASS: Case 1 border and Schur complement are certified")

    case3 = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 1, 5]])
    case3_mp = sp.Matrix([[sp.Rational(1, 2), 0, 0], [0, -5, 1], [0, 1, 0]])
    assert_mp(case3, case3_mp, "Hartwig Case 3 border")
    schur3 = sp.Matrix([[2, 0], [0, sp.Rational(-1, 5)]])
    schur3_mp = sp.Matrix([[sp.Rational(1, 2), 0], [0, -5]])
    assert_mp(schur3, schur3_mp, "Hartwig Case 3 Schur complement")
    print("PASS: Case 3 border and Schur complement are certified")

    p = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    assert p.T * p == sp.eye(3)
    assert_mp(p * case1 * p.T, p * case1_mp * p.T, "orthogonal GL_3(Q) conjugate")
    print("PASS: rational orthogonal conjugation preserves the MP packet")

    print("HARTWIG1976_SVD_MP_BORDER_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
