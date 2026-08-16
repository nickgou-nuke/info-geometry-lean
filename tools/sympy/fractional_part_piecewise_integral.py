#!/usr/bin/env python3
"""
Exact Fractional Part Piecewise Interval Integral CAS Verification.

Verifies:
1. Cell integral: int_{1/(k+1)}^{1/k} (1/x - k) dx = ln(k+1) - ln(k) - 1/(k+1) for all k >= 1.
2. Telescoping sum: sum_{k=0}^{N-1} (ln(k+2) - ln(k+1)) = ln(N+1).
3. Master cell-sum formula: sum_{k=0}^{N-1} (ln(k+2) - ln(k+1) - 1/(k+2)) = ln(N+1) - sum_{k=0}^{N-1} 1/(k+2).
4. Asymptotics towards 1 - gamma.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_fractional_part_piecewise_integral() -> None:
    print("========================================================================")
    print("FRACTIONAL PART PIECEWISE INTEGRAL: CAS VERIFICATION")
    print("========================================================================")

    x = sp.symbols("x", real=True, positive=True)

    # 1. Exact cell integrals for k = 1..10
    for k_val in range(1, 11):
        a = sp.Rational(1, k_val + 1)
        b = sp.Rational(1, k_val)
        val = sp.integrate(1 / x - k_val, (x, a, b))
        expected = sp.log(k_val + 1) - sp.log(k_val) - sp.Rational(1, k_val + 1)
        assert_zero(sp.simplify(val - expected), f"Cell integral for k={k_val}")
    print("  [OK] 1. Exact Cell Integrals int_{1/(k+1)}^{1/k} (1/x - k) dx verified")

    # 2. Telescoping log sum
    for N_val in [1, 5, 10, 50]:
        tel_sum = sum(
            sp.log(k + 2) - sp.log(k + 1)
            for k in range(N_val)
        )
        expected_tel = sp.log(N_val + 1)
        assert_zero(sp.simplify(tel_sum - expected_tel), f"Telescoping sum for N={N_val}")
    print("  [OK] 2. Exact Telescoping Logarithmic Sum sum (ln(k+2) - ln(k+1)) = ln(N+1) verified")

    # 3. Master cell-sum formula
    for N_val in [1, 5, 10, 50]:
        lhs = sum(
            sp.log(k + 2) - sp.log(k + 1) - sp.Rational(1, k + 2)
            for k in range(N_val)
        )
        rhs = sp.log(N_val + 1) - sum(sp.Rational(1, k + 2) for k in range(N_val))
        assert_zero(sp.simplify(lhs - rhs), f"Master cell sum for N={N_val}")
    print("  [OK] 3. Master Cell-Sum Formula verified")

    # 4. Asymptotics towards 1 - EulerGamma
    N_large = 1000
    approx_val = float(sum(
        sp.log(k + 2) - sp.log(k + 1) - sp.Rational(1, k + 2)
        for k in range(N_large)
    ).evalf())
    expected_limit = float((1 - sp.EulerGamma).evalf())
    diff = abs(approx_val - expected_limit)
    assert diff < 0.001, f"Asymptotic difference {diff} too large"
    print(f"  [OK] 4. Limit N -> oo matches 1 - EulerGamma (approx {approx_val:.6f} vs {expected_limit:.6f})")

    print("========================================================================")
    print("ALL FRACTIONAL PART PIECEWISE INTEGRALS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_fractional_part_piecewise_integral()
