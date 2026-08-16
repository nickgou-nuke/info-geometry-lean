#!/usr/bin/env python3
"""Zeta Log-Derivative De Rham 1-Form & Integer Period Quantization.

Mirrors:
  * `InfoGeometry.Topology.ZetaLogDerivativeDeRhamPeriodBridge`

Verifies:
  1. Logarithmic 1-form product additivity:
       omega(f1 * f2) = omega(f1) + omega(f2)
  2. Monomial zero expansion:
       omega((s - rho)^m) = - m / (s - rho)
  3. Factorization at zero of multiplicity m:
       f(s) = (s - rho)^m * g(s) ==> omega_f(s) = - m / (s - rho) + omega_g(s)
  4. Residue & Integer Period Quantization:
       Res_{s=rho}(omega_f) = - m  (in Z)
  5. V4 Klein Involutions on Zeros & Residues:
       tau(rho) = 1 - rho, sigma(rho) = conjugate(rho), gamma(rho) = 1 - conjugate(rho)
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
    print("ZETA LOG-DERIVATIVE DE RHAM 1-FORM & INTEGER PERIOD QUANTIZATION")
    print("=" * 72)

    s, rho = sp.symbols("s rho", complex=True)
    m = sp.Symbol("m", integer=True, positive=True)
    g = sp.Function("g")(s)

    # 1. Monomial logarithmic 1-form
    P = (s - rho)**m
    dP_ds = sp.diff(P, s)
    omega_P = - dP_ds / P
    expected_omega_P = - m / (s - rho)
    assert sp.simplify(omega_P - expected_omega_P) == 0
    print("  [OK] Monomial de Rham 1-form omega((s-rho)^m) = -m/(s-rho) verified")

    # 2. General Zero Multiplicity Factorization
    f = P * g
    df_ds = sp.diff(f, s)
    omega_f = - df_ds / f
    omega_g = - sp.diff(g, s) / g
    assert sp.simplify(omega_f - (expected_omega_P + omega_g)) == 0
    print("  [OK] Zero multiplicity decomposition omega_f(s) = -m/(s-rho) + omega_g(s) verified")

    # 3. Residue calculation around s = rho for concrete analytic g(s) = exp(s)
    for m_val in [1, 2, 3]:
        f_concrete = (s - rho)**m_val * sp.exp(s)
        omega_concrete = - sp.diff(f_concrete, s) / f_concrete
        res_val = sp.residue(omega_concrete, s, rho)
        assert res_val == -m_val
    print("  [OK] Residue quantization Res_{s=rho}(omega_f) = -m (integer period) verified")

    # 4. V4 Klein Involutions on Zeros
    tau = lambda z: 1 - z
    sigma = lambda z: sp.conjugate(z)
    gamma = lambda z: 1 - sp.conjugate(z)

    assert tau(tau(rho)) == rho
    assert sigma(sigma(rho)) == rho
    assert gamma(gamma(rho)) == rho
    assert gamma(rho) == tau(sigma(rho))
    print("  [OK] V4 Klein Four-Group involution algebra on zero locus verified")

    print("=" * 72)
    print("ZETA LOG-DERIVATIVE DE RHAM 1-FORM & PERIODS VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
