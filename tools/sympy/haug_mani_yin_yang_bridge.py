#!/usr/bin/env python3
"""
Finite Haug-Mani / Yin-Yang real doubled bridge witness.

This mirrors lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean with
concrete real 2 x 2 matrices.  It verifies only the finite representation
claims: two real involutions generate a square-minus-one phase axis, and
`a + bK` reproduces the ordinary complex multiplication table.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_eq(lhs: sp.Matrix, rhs: sp.Matrix, label: str) -> None:
    diff = sp.simplify(lhs - rhs)
    if diff != sp.zeros(*lhs.shape):
        raise AssertionError(f"{label} failed:\n{diff}")


def main() -> None:
    print("=" * 72)
    print("HAUG-MANI REAL DOUBLED BRIDGE -- SYMPY VERIFICATION")
    print("=" * 72)

    identity = sp.eye(2)
    mixed = sp.Matrix([[0, 1], [1, 0]])
    epsilon = sp.Matrix([[1, 0], [0, -1]])
    phase = mixed * epsilon

    physical = sp.Rational(1, 2) * (identity + epsilon)
    ghost = sp.Rational(1, 2) * (identity - epsilon)

    assert_matrix_eq(mixed * mixed, identity, "J^2 = I")
    assert_matrix_eq(epsilon * epsilon, identity, "epsilon^2 = I")
    assert_matrix_eq(mixed * epsilon + epsilon * mixed, sp.zeros(2), "J epsilon + epsilon J = 0")
    assert_matrix_eq(phase, sp.Matrix([[0, -1], [1, 0]]), "K = J epsilon")
    assert_matrix_eq(phase * phase, -identity, "K^2 = -I")
    print("  real involutions and phase axis verified")

    assert_matrix_eq(physical * physical, physical, "P+ idempotent")
    assert_matrix_eq(ghost * ghost, ghost, "P- idempotent")
    assert_matrix_eq(physical * ghost, sp.zeros(2), "P+ P- = 0")
    assert_matrix_eq(ghost * physical, sp.zeros(2), "P- P+ = 0")
    assert_matrix_eq(physical + ghost, identity, "P+ + P- = I")
    assert_matrix_eq(mixed * physical * mixed, ghost, "J P+ J = P-")
    assert_matrix_eq(mixed * ghost * mixed, physical, "J P- J = P+")
    assert_matrix_eq(mixed * phase * mixed, -phase, "J K J = -K")
    print("  doubled sign sectors verified")

    a, b, c, d = sp.symbols("a b c d", real=True)

    def scalar(x: sp.Expr, y: sp.Expr) -> sp.Matrix:
        return x * identity + y * phase

    assert_matrix_eq(scalar(0, 0), sp.zeros(2), "scalar(0,0) = 0")
    assert_matrix_eq(scalar(1, 0), identity, "scalar(1,0) = I")
    assert_matrix_eq(scalar(0, 1), phase, "scalar(0,1) = K")
    assert_matrix_eq(scalar(0, 1) * scalar(0, 1), -identity, "embedded i squares to -I")
    assert_matrix_eq(
        scalar(a, b) * scalar(c, d),
        scalar(a * c - b * d, a * d + b * c),
        "(a+bK)(c+dK) multiplication law",
    )
    assert_matrix_eq(mixed * scalar(a, b) * mixed, scalar(a, -b), "J-conjugation")

    if sp.simplify(scalar(a, b)[0, 0] - a) != 0:
        raise AssertionError("coefficient readback a failed")
    if sp.simplify(scalar(a, b)[1, 0] - b) != 0:
        raise AssertionError("coefficient readback b failed")
    print("  real doubled scalar readback verified")

    print("=" * 72)
    print("HAUG-MANI REAL DOUBLED BRIDGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
