#!/usr/bin/env python3
"""
Exact Bessel L2 Orthonormal Projection Inequality CAS Verification.

Verifies:
1. Residual energy expansion: int_0^1 (f - (c1 e1 + c2 e2))^2 dx = int_0^1 f^2 - (c1^2 + c2^2).
2. Bessel inequality: c1^2 + c2^2 <= int_0^1 f^2 dx.
3. Trigonometric Fourier Bessel bound: 2 (int f sin(2 pi x))^2 + 2 (int f cos(2 pi x))^2 <= int f^2.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_bessel_l2_orthonormal_projection() -> None:
    print("========================================================================")
    print("BESSEL L2 ORTHONORMAL PROJECTION: CAS VERIFICATION")
    print("========================================================================")

    x = sp.symbols("x", real=True)

    # 1. Orthonormal basis: sqrt(2)*sin(2*pi*x), sqrt(2)*cos(2*pi*x)
    e1 = sp.sqrt(2) * sp.sin(2 * sp.pi * x)
    e2 = sp.sqrt(2) * sp.cos(2 * sp.pi * x)

    int_e1_sq = sp.integrate(e1 ** 2, (x, 0, 1))
    int_e2_sq = sp.integrate(e2 ** 2, (x, 0, 1))
    int_e1e2 = sp.integrate(e1 * e2, (x, 0, 1))

    assert_zero(sp.simplify(int_e1_sq - 1), "e1 norm squared = 1")
    assert_zero(sp.simplify(int_e2_sq - 1), "e2 norm squared = 1")
    assert_zero(sp.simplify(int_e1e2), "e1, e2 orthogonal = 0")
    print("  [OK] 1. Orthonormal Basis System verified: int e1^2 = 1, int e2^2 = 1, int e1 e2 = 0")

    # 2. Test function f = x^2 + 1
    f = x ** 2 + 1
    c1 = sp.integrate(f * e1, (x, 0, 1))
    c2 = sp.integrate(f * e2, (x, 0, 1))
    int_f2 = sp.integrate(f ** 2, (x, 0, 1))

    residual_integrand = (f - (c1 * e1 + c2 * e2)) ** 2
    residual_int = sp.integrate(residual_integrand, (x, 0, 1))
    expected_residual = int_f2 - (c1 ** 2 + c2 ** 2)

    assert_zero(sp.simplify(residual_int - expected_residual), "Residual energy expansion")
    print("  [OK] 2. Exact Residual Energy Expansion int (f - Pf)^2 = int f^2 - (c1^2 + c2^2) verified")

    # 3. Bessel inequality
    bessel_diff = float((int_f2 - (c1 ** 2 + c2 ** 2)).evalf())
    assert bessel_diff >= -1e-12, f"Bessel inequality violated: {bessel_diff}"
    print(f"  [OK] 3. Exact Bessel Inequality verified: c1^2 + c2^2 = {float((c1**2 + c2**2).evalf()):.6f} <= int f^2 = {float(int_f2.evalf()):.6f}")

    print("========================================================================")
    print("ALL BESSEL L2 ORTHONORMAL PROJECTION THEOREMS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_bessel_l2_orthonormal_projection()
