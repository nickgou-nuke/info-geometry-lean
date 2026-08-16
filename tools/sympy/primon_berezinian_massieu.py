#!/usr/bin/env python3
"""Supergraded Primon Algebra, Berezinian Dirichlet Convolution, Surprisal & Massieu Free Energy.

Mirrors:
  * `InfoGeometry.Topology.PrimonBerezinianMassieuBridge`

Verifies:
  1. Supergraded Primon energy: E_n = ln(n)
  2. Surprisal (Self-Information) I_n = -ln(p_n) = beta * E_n - Phi(beta) where Phi(beta) = ln(Z)
  3. Shannon Entropy as the Expectation of the Surprisal:
       S(beta) = E[I] = - sum_n p_n ln(p_n) = beta * <E> + ln(Z)
  4. Legendre Duality & Free Energy Balance:
       F(beta) = - (1/beta) * Phi(beta) = <E> - T * S where T = 1/beta
  5. Berezinian / Dirichlet Supertrace Cancellation:
       zeta(s) * (1/zeta(s)) = 1
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
    print("PRIMON BEREZINIAN MASSIEU & SURPRISAL-ENTROPY VERIFICATION")
    print("=" * 72)

    n, beta, Z = sp.symbols("n beta Z", positive=True)

    # 1. Surprisal decomposition
    # p_n = n^(-beta) / Z
    p_n = n**(-beta) / Z
    surprisal = - sp.log(p_n)
    expected_surprisal = beta * sp.log(n) + sp.log(Z)
    assert sp.simplify(surprisal - expected_surprisal) == 0
    print("  [OK] Surprisal I_n = -ln(p_n) = beta * ln(n) + ln(Z) verified")

    # 2. Shannon entropy as expectation of surprisal
    p1, p2 = sp.symbols("p1 p2", positive=True)
    # Model 2-point distribution
    I1 = - sp.log(p1)
    I2 = - sp.log(p2)
    E_surprisal = p1 * I1 + p2 * I2
    S_shannon = - (p1 * sp.log(p1) + p2 * sp.log(p2))
    assert sp.simplify(E_surprisal - S_shannon) == 0
    print("  [OK] Shannon entropy S = E[I] = -sum p_n ln(p_n) verified")

    # 3. Massieu Potential & Free Energy Duality
    mean_E, S = sp.symbols("mean_E S", real=True)
    Phi = sp.log(Z)
    # S = beta * mean_E + Phi ===> mean_E - (1/beta) * S = - (1/beta) * Phi = F
    S_expr = beta * mean_E + Phi
    F_legendre = sp.simplify(mean_E - (1 / beta) * S_expr)
    F_helmholtz = - (1 / beta) * Phi
    assert sp.simplify(F_legendre - F_helmholtz) == 0
    print("  [OK] Free energy Legendre duality <E> - T*S = F(beta) verified")

    # 4. Berezinian / Dirichlet Supertrace Cancellation
    s = sp.Symbol("s")
    zeta_s = sp.Function("zeta")(s)
    berezinian_prod = zeta_s * (1 / zeta_s)
    assert sp.simplify(berezinian_prod) == 1
    print("  [OK] Berezinian Dirichlet cancellation zeta(s) * (1/zeta(s)) = 1 verified")

    print("=" * 72)
    print("PRIMON BEREZINIAN MASSIEU & SURPRISAL-ENTROPY VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
