#!/usr/bin/env sage -python
"""
Exact Sage certificate for Hartwig 1976 SVD / Moore--Penrose bordered
matrices.  All arithmetic is over QQ.
"""

from __future__ import annotations

from sage.all import Matrix, QQ, identity_matrix, zero_matrix


def assert_zero_matrix(m, label: str) -> None:
    if m != zero_matrix(QQ, m.nrows(), m.ncols()):
        raise AssertionError(f"{label} failed:\n{m}")


def assert_mp(a, x, label: str) -> None:
    assert_zero_matrix(a * x * a - a, f"{label}: A X A = A")
    assert_zero_matrix(x * a * x - x, f"{label}: X A X = X")
    assert_zero_matrix((a * x).transpose() - a * x, f"{label}: (A X)^* = A X")
    assert_zero_matrix((x * a).transpose() - x * a, f"{label}: (X A)^* = X A")


def main() -> None:
    print("=== Hartwig 1976 SVD / Moore--Penrose bordered Sage certificate ===")

    base_a = Matrix(QQ, [[2, 0], [0, 0]])
    base_mp = Matrix(QQ, [[QQ(1) / 2, 0], [0, 0]])
    assert_mp(base_a, base_mp, "base SVD block")

    case1 = Matrix(QQ, [[2, 0, 3], [0, 0, 0], [1, 0, 5]])
    case1_mp = Matrix(QQ, [[QQ(5) / 7, 0, QQ(-3) / 7], [0, 0, 0], [QQ(-1) / 7, 0, QQ(2) / 7]])
    z = QQ(5) - QQ(1) * QQ(1) / 2 * QQ(3)
    assert z == QQ(7) / 2
    assert_mp(case1, case1_mp, "Hartwig Case 1 border")
    assert_mp(Matrix(QQ, [[QQ(7) / 5, 0], [0, 0]]), Matrix(QQ, [[QQ(5) / 7, 0], [0, 0]]),
              "Hartwig Case 1 Schur complement")
    print("PASS: Case 1 border and Schur complement are certified")

    case3 = Matrix(QQ, [[2, 0, 0], [0, 0, 1], [0, 1, 5]])
    case3_mp = Matrix(QQ, [[QQ(1) / 2, 0, 0], [0, -5, 1], [0, 1, 0]])
    assert_mp(case3, case3_mp, "Hartwig Case 3 border")
    assert_mp(Matrix(QQ, [[2, 0], [0, QQ(-1) / 5]]), Matrix(QQ, [[QQ(1) / 2, 0], [0, -5]]),
              "Hartwig Case 3 Schur complement")
    print("PASS: Case 3 border and Schur complement are certified")

    p = Matrix(QQ, [[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    assert p.transpose() * p == identity_matrix(QQ, 3)
    assert_mp(p * case1 * p.transpose(), p * case1_mp * p.transpose(),
              "orthogonal GL_3(Q) conjugate")
    print("PASS: rational orthogonal conjugation preserves the MP packet")

    print("HARTWIG1976_SVD_MP_BORDER_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
