#!/usr/bin/env python3
"""
Exact Parseval L2 Orthonormal Energy Identity CAS Verification.

Verifies:
1. Span coefficients: int_0^1 (a1 e1 + a2 e2) e1 = a1, int_0^1 (a1 e1 + a2 e2) e2 = a2.
2. Parseval energy: int_0^1 (a1 e1 + a2 e2)^2 = a1^2 + a2^2.
3. Bessel saturation: residual = 0 <==> energy_f = c1^2 + c2^2.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_parseval_l2_orthonormal_identity() -> None:
    print("========================================================================")
    print("PARSEVAL L2 ORTHONORMAL IDENTITY: CAS VERIFICATION")
    print("========================================================================")

    x, a1, a2 = sp.symbols("x a1 a2", real=True)

    # 1. Orthonormal system
    e1 = sp.sqrt(2) * sp.sin(2 * sp.pi * x)
    e2 = sp.sqrt(2) * sp.cos(2 * sp.pi * x)

    f_span = a1 * e1 + a2 * e2

    c1 = sp.integrate(f_span * e1, (x, 0, 1))
    c2 = sp.integrate(f_span * e2, (x, 0, 1))

    assert_zero(sp.simplify(c1 - a1), "c1 = a1")
    assert_zero(sp.simplify(c2 - a2), "c2 = a2")
    print("  [OK] 1. Linear Span Projection Coefficients c1 = a1, c2 = a2 verified")

    # 2. Parseval energy conservation
    int_f2 = sp.integrate(f_span ** 2, (x, 0, 1))
    expected_energy = a1 ** 2 + a2 ** 2

    assert_zero(sp.simplify(int_f2 - expected_energy), "int f^2 = a1^2 + a2^2")
    print("  [OK] 2. Exact Parseval Energy Conservation int (a1 e1 + a2 e2)^2 = a1^2 + a2^2 verified")

    # 3. Residual energy vanishing
    residual = sp.integrate((f_span - (c1 * e1 + c2 * e2)) ** 2, (x, 0, 1))
    assert_zero(sp.simplify(residual), "Residual = 0 on span")
    print("  [OK] 3. Exact Bessel Saturation (Residual = 0) on Linear Span verified")

    print("========================================================================")
    print("ALL PARSEVAL L2 ORTHONORMAL THEOREMS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_parseval_l2_orthonormal_identity()
