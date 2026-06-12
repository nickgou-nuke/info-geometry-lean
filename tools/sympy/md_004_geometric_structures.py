#!/usr/bin/env python3
"""Finite witness for MD 004 geometric structures.

Mirrors `InfoGeometry.Physics.MD004GeometricStructures`.

Verified theorem-safe content only:
* coordinate complex structures I,J,K on R^4 square to -1;
* I,J,K satisfy quaternion multiplication signs;
* I,J,K preserve the Euclidean coordinate metric;
* fundamental forms omega_A(x,y)=g(Ax,y) are skew-symmetric;
* the ambient standard complex structure J0 on C^4 ~= R^8 has the same finite
  square/metric/skew-form properties.

No smooth integrability, Levi-Civita, curvature, closed differential-form,
Ricci-flatness, Kähler-Einstein, or symplectic-manifold theorem is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def dot(u: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return (u.T * v)[0]


def main() -> int:
    print("=" * 72)
    print("MD 004 FINITE GEOMETRIC STRUCTURES")
    print("=" * 72)

    I4 = sp.Matrix([[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]])
    J4 = sp.Matrix([[0, 0, -1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, -1, 0, 0]])
    K4 = sp.Matrix([[0, 0, 0, -1], [0, 0, -1, 0], [0, 1, 0, 0], [1, 0, 0, 0]])
    eye4 = sp.eye(4)

    assert_matrix_zero(I4 * I4 + eye4, "I^2 = -1")
    assert_matrix_zero(J4 * J4 + eye4, "J^2 = -1")
    assert_matrix_zero(K4 * K4 + eye4, "K^2 = -1")
    assert_matrix_zero(I4 * J4 - K4, "IJ = K")
    assert_matrix_zero(J4 * K4 - I4, "JK = I")
    assert_matrix_zero(K4 * I4 - J4, "KI = J")
    assert_matrix_zero(J4 * I4 + K4, "JI = -K")
    assert_matrix_zero(K4 * J4 + I4, "KJ = -I")
    assert_matrix_zero(I4 * K4 + J4, "IK = -J")
    print("R4 quaternion complex-structure relations: OK")

    a = sp.Matrix(sp.symbols("a0:4"))
    b = sp.Matrix(sp.symbols("b0:4"))
    for name, A in [("I", I4), ("J", J4), ("K", K4)]:
        assert_zero(dot(A * a, A * b) - dot(a, b), f"{name} metric preservation")
        omega_ab = dot(A * a, b)
        omega_ba = dot(A * b, a)
        assert_zero(omega_ba + omega_ab, f"omega_{name} skew")
    print("R4 metric preservation and skew forms: OK")

    J0 = sp.zeros(8)
    for k in range(4):
        J0[2 * k, 2 * k + 1] = -1
        J0[2 * k + 1, 2 * k] = 1
    eye8 = sp.eye(8)
    u = sp.Matrix(sp.symbols("u0:8"))
    v = sp.Matrix(sp.symbols("v0:8"))
    assert_matrix_zero(J0 * J0 + eye8, "ambient J0^2 = -1")
    assert_zero(dot(J0 * u, J0 * v) - dot(u, v), "ambient J0 metric preservation")
    assert_zero(dot(J0 * v, u) + dot(J0 * u, v), "ambient omega0 skew")
    print("ambient C4/R8 standard complex structure: OK")

    print("=" * 72)
    print("MD 004 FINITE GEOMETRIC STRUCTURES VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
