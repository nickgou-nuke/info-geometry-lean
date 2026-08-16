#!/usr/bin/env python3
"""Möbius Continuous Lie Flow Classification (Hyperbolic, Elliptic, Parabolic, Loxodromic) SymPy Verification.

Mirrors:
  * `InfoGeometry.Topology.MobiusLieFlowClassificationBridge`

Verifies:
  1. Hyperbolic Lie Flow:
       Phi_t(z) = exp(lambda * t) * z,  group law: Phi_{t1+t2} = Phi_t1 o Phi_t2
  2. Elliptic Lie Flow:
       Phi_t(z) = exp(i * theta * t) * z,  group law: Phi_{t1+t2} = Phi_t1 o Phi_t2
  3. Parabolic Lie Flow:
       Phi_t(z) = z + c * t,  group law: Phi_{t1+t2} = Phi_t1 o Phi_t2
  4. Loxodromic Lie Flow & Commuting Factorization:
       Phi_t(z) = exp((lambda + i * theta) * t) * z = Phi_t^{hyp}(Phi_t^{ell}(z))
  5. Commutativity of Hyperbolic & Elliptic Flow Sectors:
       Phi_{t1}^{hyp} o Phi_{t2}^{ell} = Phi_{t2}^{ell} o Phi_{t1}^{hyp}
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
    print("MÖBIUS CONTINUOUS LIE FLOW CLASSIFICATION (HYP, ELL, PAR, LOX) VERIFICATION")
    print("=" * 72)

    z = sp.Symbol("z")
    t1, t2 = sp.symbols("t1 t2", real=True)
    lam = sp.Symbol("lambda", real=True)
    theta = sp.Symbol("theta", real=True)
    c = sp.Symbol("c")

    # 1. Hyperbolic Flow
    def phi_hyp(t_val, z_val):
        return sp.exp(lam * t_val) * z_val

    assert sp.simplify(phi_hyp(t1 + t2, z) - phi_hyp(t1, phi_hyp(t2, z))) == 0
    assert sp.simplify(phi_hyp(0, z) - z) == 0
    print("  [OK] Hyperbolic 1-parameter Lie flow group law verified")

    # 2. Elliptic Flow
    def phi_ell(t_val, z_val):
        return sp.exp(sp.I * theta * t_val) * z_val

    assert sp.simplify(phi_ell(t1 + t2, z) - phi_ell(t1, phi_ell(t2, z))) == 0
    assert sp.simplify(phi_ell(0, z) - z) == 0
    print("  [OK] Elliptic 1-parameter Lie flow group law verified")

    # 3. Parabolic Flow
    def phi_par(t_val, z_val):
        return z_val + c * t_val

    assert sp.simplify(phi_par(t1 + t2, z) - phi_par(t1, phi_par(t2, z))) == 0
    assert sp.simplify(phi_par(0, z) - z) == 0
    print("  [OK] Parabolic 1-parameter Lie flow group law verified")

    # 4. Loxodromic Flow & Commuting Factorization
    def phi_lox(t_val, z_val):
        return sp.exp((lam + sp.I * theta) * t_val) * z_val

    assert sp.simplify(phi_lox(t1 + t2, z) - phi_lox(t1, phi_lox(t2, z))) == 0
    assert sp.simplify(phi_lox(t1, z) - phi_hyp(t1, phi_ell(t1, z))) == 0
    print("  [OK] Loxodromic Lie flow group law & rotor factorization verified")

    # 5. Commutativity
    assert sp.simplify(phi_hyp(t1, phi_ell(t2, z)) - phi_ell(t2, phi_hyp(t1, z))) == 0
    print("  [OK] Commutativity of hyperbolic and elliptic flow generators verified")

    print("=" * 72)
    print("MÖBIUS CONTINUOUS LIE FLOW CLASSIFICATION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
