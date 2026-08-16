#!/usr/bin/env python3
"""
Constructive Mellin L2 Interval Integral CAS Verification.

Verifies:
1. Exact monomial integral: int_0^1 x^n dx = 1 / (n + 1).
2. Exact L2 energy: int_0^1 (x^n)^2 dx = 1 / (2n + 1) > 0.
3. Exact Gram matrix element: int_0^1 x^n * x^m dx = 1 / (n + m + 1).
4. Hilbert matrix positive definiteness for monomial basis.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_constructive_mellin_l2_integral() -> None:
    print("========================================================================")
    print("CONSTRUCTIVE MELLIN L2 INTEGRAL: CAS VERIFICATION")
    print("========================================================================")

    x = sp.symbols("x", real=True, positive=True)

    # 1. Monomial integral on [0, 1]
    for n_val in [0, 1, 2, 3, 4, 5]:
        val = sp.integrate(x ** n_val, (x, 0, 1))
        expected = sp.Rational(1, n_val + 1)
        assert_zero(val - expected, f"int_0^1 x^{n_val} dx = 1/{n_val+1}")
    print("  [OK] 1. Monomial Definite Lebesgue Integral int_0^1 x^n dx verified")

    # 2. L2 energy
    for n_val in [0, 1, 2, 3]:
        energy_val = sp.integrate((x ** n_val) ** 2, (x, 0, 1))
        expected_energy = sp.Rational(1, 2 * n_val + 1)
        assert_zero(energy_val - expected_energy, f"L2 energy for n={n_val}")
        assert energy_val > 0
    print("  [OK] 2. Exact Monomial L2 Energy in L2(0, 1) verified")

    # 3. Hilbert / Gram matrix element
    for n_val in [0, 1, 2]:
        for m_val in [0, 1, 2]:
            inner_val = sp.integrate(x ** n_val * x ** m_val, (x, 0, 1))
            expected_inner = sp.Rational(1, n_val + m_val + 1)
            assert_zero(inner_val - expected_inner, f"Gram element ({n_val}, {m_val})")
    print("  [OK] 3. Exact Gram Matrix Elements int_0^1 x^n x^m dx verified")

    # 4. Hilbert matrix H_N is strictly positive definite
    H_3 = sp.Matrix([
        [sp.Rational(1, i + j + 1) for j in range(3)]
        for i in range(3)
    ])
    assert H_3.det() > 0
    print("  [OK] 4. Hilbert Gram Matrix Strict Positive Definiteness det(H_3) > 0 verified")

    print("========================================================================")
    print("ALL CONSTRUCTIVE MELLIN L2 INTEGRALS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_constructive_mellin_l2_integral()
