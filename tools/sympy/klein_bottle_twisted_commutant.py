#!/usr/bin/env python3
"""
Symbolic CAS verification of the Klein Bottle Group and Twisted Commutant Algebra.

Verifies:
1. Fundamental group presentation: bab⁻¹ = a⁻¹ on the Klein bottle.
2. Even winding central commutant: b² a b⁻² = a.
3. Twisted Intertwiner Action: U a U⁻¹ = α(a) with α² = id.
4. Z₂-graded Commutant Multiplication table:
   C₀ · C₀ ⊆ C₀, C₀ · C₁ ⊆ C₁, C₁ · C₀ ⊆ C₁, C₁ · C₁ ⊆ C₀.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero, assert_matrix_zero


def test_klein_bottle_algebra() -> None:
    print("=== Klein Bottle Twisted Commutant Algebra Verification ===")

    # 1. Circle coordinate and parity involution α(z) = z⁻¹
    z = sp.Symbol("z", nonzero=True)
    alpha = lambda expr: expr.subs(z, 1 / z)

    assert_zero(sp.simplify(alpha(alpha(z)) - z), "Involution property α² = id")
    print("  [PASS] Base automorphism satisfies α² = id")

    # 2. Representation of Klein generators via 2x2 grading matrices:
    # A acts diagonally (C₀ sector), Glide operator U acts off-diagonally (C₁ sector)
    # A = diag(z, z⁻¹), U = [[0, 1], [1, 0]] (grading flip)
    A = sp.Matrix([[z, 0], [0, 1 / z]])
    U = sp.Matrix([[0, 1], [1, 0]])

    # U A U⁻¹
    U_inv = U.inv()
    U_A_Uinv = sp.simplify(U * A * U_inv)
    alpha_A = sp.Matrix([[1 / z, 0], [0, z]])

    assert_matrix_zero(sp.simplify(U_A_Uinv - alpha_A), "Twisted intertwining U A U⁻¹ = α(A)")
    print("  [PASS] Twisted Intertwining: U A U⁻¹ = α(A)")

    # 3. Double Cover Even Sector: U² = I₂
    U2 = sp.simplify(U * U)
    I2 = sp.eye(2)
    assert_matrix_zero(sp.simplify(U2 - I2), "Even winding U² = I")
    assert_matrix_zero(sp.simplify(U2 * A - A * U2), "Central commutativity [U², A] = 0")
    print("  [PASS] Even Sector Recovery: [U², A] = 0 on double cover (2-torus)")

    # 4. Z₂-graded Commutant Multiplication
    # C₀: Matrices commuting with A (diagonal)
    # C₁: Matrices twisted-commuting with A (anti-diagonal)
    t0_1, t0_2, t1_1, t1_2 = sp.symbols("t0_1 t0_2 t1_1 t1_2")
    C0 = sp.Matrix([[t0_1, 0], [0, t0_2]])
    C1 = sp.Matrix([[0, t1_1], [t1_2, 0]])

    # C₀ · C₀ is diagonal (C₀)
    c0_c0 = C0 * C0
    assert_zero(c0_c0[0, 1], "C₀ · C₀ is diagonal")
    assert_zero(c0_c0[1, 0], "C₀ · C₀ is diagonal")
    print("  [PASS] C₀ · C₀ ⊆ C₀")

    # C₀ · C₁ is anti-diagonal (C₁)
    c0_c1 = C0 * C1
    assert_zero(c0_c1[0, 0], "C₀ · C₁ is anti-diagonal")
    assert_zero(c0_c1[1, 1], "C₀ · C₁ is anti-diagonal")
    print("  [PASS] C₀ · C₁ ⊆ C₁")

    # C₁ · C₀ is anti-diagonal (C₁)
    c1_c0 = C1 * C0
    assert_zero(c1_c0[0, 0], "C₁ · C₀ is anti-diagonal")
    assert_zero(c1_c0[1, 1], "C₁ · C₀ is anti-diagonal")
    print("  [PASS] C₁ · C₀ ⊆ C₁")

    # C₁ · C₁ is diagonal (C₀)
    c1_c1 = C1 * C1
    assert_zero(c1_c1[0, 1], "C₁ · C₁ is diagonal")
    assert_zero(c1_c1[1, 0], "C₁ · C₁ is diagonal")
    print("  [PASS] C₁ · C₁ ⊆ C₀")

    print("\n🏆 ALL KLEIN BOTTLE TWISTED COMMUTANT THEOREMS VERIFIED!")


if __name__ == "__main__":
    test_klein_bottle_algebra()
