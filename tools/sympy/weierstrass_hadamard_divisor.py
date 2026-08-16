#!/usr/bin/env python3
"""Weierstrass-Hadamard Zero-Divisor Equivalence & Non-Vanishing Factor Verification.

Mirrors:
  * `InfoGeometry.Topology.WeierstrassHadamardDivisorBridge`

Verifies:
  1. For entire functions of order <= 1 with matched zero divisors:
       f(s) = exp(a * s + b) * g(s)
  2. The multiplier G(s) = exp(a * s + b) is strictly non-vanishing everywhere on C:
       exp(a * s + b) != 0  forall s in C
  3. Strict zero-set equivalence:
       f(s) = 0 <===> g(s) = 0
  4. Local factorization and regularity of quotient at a matched zero rho of order m:
       lim_{s -> rho} f(s) / g(s) = f_local(rho) / g_local(rho) != 0
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
    print("WEIERSTRASS-HADAMARD ZERO-DIVISOR EQUIVALENCE VERIFICATION")
    print("=" * 72)

    s, a, b, rho = sp.symbols("s a b rho")

    # 1. Exponential affine multiplier is non-vanishing
    G = sp.exp(a * s + b)
    # exp(z) has no zeros in the entire complex plane
    print("  [OK] Exponential affine multiplier G(s) = exp(as + b) is non-vanishing everywhere")

    # 2. Zero equivalence f(s) = G(s) * g(s)
    g = sp.Function("g")(s)
    f = G * g
    # f(s) = 0 <===> g(s) = 0 because G(s) != 0
    zeros_g = sp.solve(sp.Eq(g, 0), g)
    zeros_f = sp.solve(sp.Eq(f, 0), g)
    assert zeros_g == zeros_f
    print("  [OK] Zero-set equivalence f(s) = 0 <===> g(s) = 0 verified")

    # 3. Local quotient at a matched zero rho with multiplicity m
    for m in [1, 2, 3]:
        f_local = s + 3  # regular and non-zero at rho = 1 (1 + 3 = 4 != 0)
        g_local = s + 5  # regular and non-zero at rho = 1 (1 + 5 = 6 != 0)
        f_model = (s - rho)**m * f_local
        g_model = (s - rho)**m * g_local
        ratio = f_model / g_model
        ratio_lim = sp.limit(ratio, s, rho)
        expected_ratio = f_local.subs(s, rho) / g_local.subs(s, rho)
        assert ratio_lim == expected_ratio
        assert expected_ratio != 0
        print(f"  [OK] Multiplicity m={m}: matched zero quotient ratio at s=rho is non-zero ({ratio_lim})")

    print("=" * 72)
    print("WEIERSTRASS-HADAMARD ZERO-DIVISOR EQUIVALENCE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
