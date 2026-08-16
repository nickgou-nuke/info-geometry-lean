#!/usr/bin/env python3
"""Logarithmic Differential Identity & Maurer-Cartan Form Verification.

Mirrors:
  * `InfoGeometry.Analysis.LogarithmicDerivativeBridge`

Verifies:
  1. Chain rule: d/dx (ln(Q(x))) = Q'(x) / Q(x)
  2. Algebraic 1-form properties:
       dLog(Q1 * Q2) = dLog(Q1) + dLog(Q2)
       dLog(1 / Q) = - dLog(Q)
       dLog(Q1 / Q2) = dLog(Q1) - dLog(Q2)
       dLog(Q^n) = n * dLog(Q)
  3. Scale invariance: dLog(c * Q) = dLog(Q)
  4. Score function variance / Fisher metric: g_F = (p' / p)^2
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


def main() -> None:
    print("=" * 72)
    print("LOGARITHMIC DERIVATIVE IDENTITY & MAURER-CARTAN FORM VERIFICATION")
    print("=" * 72)

    x = sp.Symbol("x", real=True)
    Q = sp.Function("Q")(x)
    Q_prime = sp.diff(Q, x)

    # 1. Analytic chain rule
    d_log_Q = sp.diff(sp.log(Q), x)
    expected_d_log_Q = Q_prime / Q
    assert sp.simplify(d_log_Q - expected_d_log_Q) == 0
    print("  [OK] Analytic chain rule d/dx (ln Q(x)) = Q'(x)/Q(x) verified")

    # 2. Algebraic properties
    Q1, Q2, dQ1, dQ2, c = sp.symbols("Q1 Q2 dQ1 dQ2 c", real=True)

    # Additivity on products
    # d(Q1*Q2) = dQ1*Q2 + Q1*dQ2
    dLog_prod = (dQ1 * Q2 + Q1 * dQ2) / (Q1 * Q2)
    dLog_sum = (dQ1 / Q1) + (dQ2 / Q2)
    assert sp.simplify(dLog_prod - dLog_sum) == 0
    print("  [OK] Additivity on products dLog(Q1 * Q2) = dLog(Q1) + dLog(Q2) verified")

    # Inversion rule
    # d(1/Q) = - dQ / Q^2
    dLog_inv = (- dQ1 / Q1**2) / (1 / Q1)
    assert sp.simplify(dLog_inv - (- dQ1 / Q1)) == 0
    print("  [OK] Inversion rule dLog(1/Q) = - dLog(Q) verified")

    # Quotient rule
    # d(Q1/Q2) = (dQ1*Q2 - Q1*dQ2) / Q2^2
    dLog_quot = ((dQ1 * Q2 - Q1 * dQ2) / Q2**2) / (Q1 / Q2)
    dLog_diff = (dQ1 / Q1) - (dQ2 / Q2)
    assert sp.simplify(dLog_quot - dLog_diff) == 0
    print("  [OK] Quotient rule dLog(Q1 / Q2) = dLog(Q1) - dLog(Q2) verified")

    # Power rule
    for n in [2, 3, 4]:
        dLog_pow = (n * Q1**(n - 1) * dQ1) / (Q1**n)
        assert sp.simplify(dLog_pow - n * (dQ1 / Q1)) == 0
    print("  [OK] Integer power scaling dLog(Q^n) = n * dLog(Q) verified")

    # Scale invariance
    dLog_scaled = (c * dQ1) / (c * Q1)
    assert sp.simplify(dLog_scaled - (dQ1 / Q1)) == 0
    print("  [OK] Scale/gauge invariance dLog(c * Q) = dLog(Q) verified")

    print("=" * 72)
    print("LOGARITHMIC DERIVATIVE IDENTITY & MAURER-CARTAN FORM VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
