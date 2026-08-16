#!/usr/bin/env python3
"""
Genuine Hadamard Factor Logarithmic Derivative CAS Verification.

Verifies:
1. Derivative of linear factor: d/ds (1 - s/rho) = -1/rho.
2. Logarithmic derivative: [d/ds (1 - s/rho)] / (1 - s/rho) = 1 / (s - rho).
3. Product rule: [d/ds (f * g)] / (f * g) = f'/f + g'/g.
4. Two-factor product: [d/ds ((1 - s/rho_1)(1 - s/rho_2))] / ((1 - s/rho_1)(1 - s/rho_2)) = 1/(s - rho_1) + 1/(s - rho_2).
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_hadamard_factor_log_deriv() -> None:
    print("========================================================================")
    print("HADAMARD FACTOR LOGARITHMIC DERIVATIVE: CAS VERIFICATION")
    print("========================================================================")

    s, rho, rho1, rho2 = sp.symbols("s rho rho1 rho2", complex=True)

    # 1. Single factor derivative
    factor = 1 - s / rho
    dfactor = sp.diff(factor, s)
    assert_zero(sp.simplify(dfactor - (-1 / rho)), "d/ds (1 - s/rho) = -1/rho")
    print("  [OK] 1. Exact Single Hadamard Factor Derivative d/ds (1 - s/rho) = -1/rho verified")

    # 2. Logarithmic derivative ratio
    log_ratio = dfactor / factor
    expected_ratio = 1 / (s - rho)
    assert_zero(sp.simplify(log_ratio - expected_ratio), "f'/f = 1 / (s - rho)")
    print("  [OK] 2. Exact Logarithmic Derivative Ratio f'/f = 1 / (s - rho) verified")

    # 3. Product rule
    f = sp.Function("f")(s)
    g = sp.Function("g")(s)
    prod_ratio = sp.diff(f * g, s) / (f * g)
    expected_prod = sp.diff(f, s) / f + sp.diff(g, s) / g
    assert_zero(sp.simplify(prod_ratio - expected_prod), "(f g)' / (f g) = f'/f + g'/g")
    print("  [OK] 3. General Product Rule for Logarithmic Derivatives verified")

    # 4. Two-factor product
    P2 = (1 - s / rho1) * (1 - s / rho2)
    P2_log_ratio = sp.diff(P2, s) / P2
    expected_P2 = 1 / (s - rho1) + 1 / (s - rho2)
    assert_zero(sp.simplify(P2_log_ratio - expected_P2), "P2'/P2 = 1/(s - rho1) + 1/(s - rho2)")
    print("  [OK] 4. Exact Two-Root Hadamard Product Logarithmic Derivative verified")

    print("========================================================================")
    print("ALL HADAMARD FACTOR LOGARITHMIC DERIVATIVES 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_hadamard_factor_log_deriv()
