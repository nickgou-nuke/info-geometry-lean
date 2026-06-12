#!/usr/bin/env python3
"""Finite witness for MD 006 operator algebra and eigenoperators.

Mirrors `InfoGeometry.Physics.MD006OperatorEigenoperators`.

Verified theorem-safe content only:
* left/right multiplication composition and commutation;
* matrix-unit joint eigenoperator identities for σ3;
* matrix-unit projectors/nilpotents and cross products;
* Pauli decompositions of E_ij;
* complex-biquaternion representatives of E_ij;
* sl2 root-vector commutators.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def mat2(prefix: str) -> sp.Matrix:
    return sp.Matrix(2, 2, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))


def comm(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def main() -> int:
    print("=" * 72)
    print("MD 006 FINITE OPERATOR/EIGENOPERATOR ALGEBRA")
    print("=" * 72)

    A = mat2("A")
    B = mat2("B")
    X = mat2("X")

    assert_matrix_zero(A * (B * X) - (A * B) * X, "left multiplication composition")
    assert_matrix_zero((X * B) * A - X * (B * A), "right multiplication composition")
    assert_matrix_zero(A * (X * B) - (A * X) * B, "left/right multiplication commute")
    assert_matrix_zero(A * (B * X) - B * (A * X) - comm(A, B) * X, "left commutator action")
    assert_matrix_zero((X * B) * A - (X * A) * B - X * comm(B, A), "right commutator action")
    print("left/right multiplication algebra: OK")

    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    E11 = sp.Matrix([[1, 0], [0, 0]])
    E12 = sp.Matrix([[0, 1], [0, 0]])
    E21 = sp.Matrix([[0, 0], [1, 0]])
    E22 = sp.Matrix([[0, 0], [0, 1]])

    eigen_data = [
        (E11, 1, 1, "E11"),
        (E12, 1, -1, "E12"),
        (E21, -1, 1, "E21"),
        (E22, -1, -1, "E22"),
    ]
    for E, lamL, lamR, name in eigen_data:
        assert_matrix_zero(s3 * E - lamL * E, f"{name} left σ3 eigen")
        assert_matrix_zero(E * s3 - lamR * E, f"{name} right σ3 eigen")
    print("matrix-unit joint eigenoperators: OK")

    assert_matrix_zero(E11 * E11 - E11, "E11 projector")
    assert_matrix_zero(E22 * E22 - E22, "E22 projector")
    assert_matrix_zero(E12 * E12, "E12 nilpotent")
    assert_matrix_zero(E21 * E21, "E21 nilpotent")
    assert_matrix_zero(E12 * E21 - E11, "E12 E21 = E11")
    assert_matrix_zero(E21 * E12 - E22, "E21 E12 = E22")
    print("matrix-unit products/projectors/nilpotents: OK")

    assert_matrix_zero(E11 - sp.Rational(1, 2) * (I2 + s3), "E11 Pauli decomposition")
    assert_matrix_zero(E22 - sp.Rational(1, 2) * (I2 - s3), "E22 Pauli decomposition")
    assert_matrix_zero(E12 - sp.Rational(1, 2) * (s1 + sp.I * s2), "E12 Pauli decomposition")
    assert_matrix_zero(E21 - sp.Rational(1, 2) * (s1 - sp.I * s2), "E21 Pauli decomposition")
    print("Pauli decompositions: OK")

    def biquat_matrix(q0: sp.Expr, q1: sp.Expr, q2: sp.Expr, q3: sp.Expr) -> sp.Matrix:
        return q0 * I2 - sp.I * q1 * s1 - sp.I * q2 * s2 - sp.I * q3 * s3

    assert_matrix_zero(E11 - biquat_matrix(sp.Rational(1, 2), 0, 0, sp.I / 2), "E11 biquaternion representative")
    assert_matrix_zero(E22 - biquat_matrix(sp.Rational(1, 2), 0, 0, -sp.I / 2), "E22 biquaternion representative")
    assert_matrix_zero(E12 - biquat_matrix(0, sp.I / 2, -sp.Rational(1, 2), 0), "E12 biquaternion representative")
    assert_matrix_zero(E21 - biquat_matrix(0, sp.I / 2, sp.Rational(1, 2), 0), "E21 biquaternion representative")
    print("complex-biquaternion representatives: OK")

    assert_matrix_zero(comm(s3, E12) - 2 * E12, "[σ3,E12]=2E12")
    assert_matrix_zero(comm(s3, E21) + 2 * E21, "[σ3,E21]=-2E21")
    assert_matrix_zero(comm(E12, E21) - s3, "[E12,E21]=σ3")
    print("sl2 root commutators: OK")

    print("=" * 72)
    print("MD 006 FINITE OPERATOR/EIGENOPERATOR ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
