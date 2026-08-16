#!/usr/bin/env python3
"""Native Mathlib 2D Flow-Adapted Coordinates, Klein V4 Symmetries & Metriplectic Dynamics on C.

Mirrors:
  * `InfoGeometry.Topology.NativeMathlibZetaMetriplecticFlowBridge`

Verifies:
  1. Coordinate Isomorphisms:
       fromCentered(toCentered(s)) = s
       toCentered(fromCentered(w)) = w
  2. Klein Four-Group V4 Symmetries:
       tau^2 = id, sigma^2 = id, gamma^2 = id
       tau o sigma = sigma o tau = gamma
  3. Critical Line Fixed Locus:
       gamma(s) = s <===> Re(s) = 1/2 <===> Re(w) = 0
  4. 2D Continuous Flow Lie Algebra:
       Phi_{t1+t2}^H = Phi_{t1}^H o Phi_{t2}^H (Hamiltonian vertical flow)
       Phi_{lam1+lam2}^S = Phi_{lam1}^S o Phi_{lam2}^S (Dissipative horizontal flow)
       Phi_t^H o Phi_lam^S = Phi_lam^S o Phi_t^H
  5. Casimir Invariance & Critical Leaf:
       Re(Phi_t^H(s)) = Re(s)
       Re(s) = 1/2 ===> Re(Phi_t^H(s)) = 1/2
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
    print("NATIVE MATHLIB ZETA METRIPLECTIC FLOW VERIFICATION")
    print("=" * 72)

    # 1. Coordinate Isomorphisms
    s = sp.Symbol("s")
    w = sp.Symbol("w")
    to_centered = lambda z: z - sp.Rational(1, 2)
    from_centered = lambda z: z + sp.Rational(1, 2)

    assert sp.simplify(from_centered(to_centered(s)) - s) == 0
    assert sp.simplify(to_centered(from_centered(w)) - w) == 0
    print("  [OK] Centered coordinate isomorphisms fromCentered o toCentered = id verified")

    # 2. Klein Four-Group V4 Symmetries
    tau = lambda z: 1 - z
    sigma = lambda z: sp.conjugate(z)
    gamma = lambda z: 1 - sp.conjugate(z)

    assert sp.simplify(tau(tau(s)) - s) == 0
    assert sp.simplify(sigma(sigma(s)) - s) == 0
    assert sp.simplify(gamma(gamma(s)) - s) == 0
    assert sp.simplify(tau(sigma(s)) - gamma(s)) == 0
    assert sp.simplify(sigma(tau(s)) - gamma(s)) == 0
    print("  [OK] Klein V4 group relations (tau^2 = sigma^2 = gamma^2 = id, tau o sigma = gamma) verified")

    # 3. Critical Line Fixed Locus
    sigma_val = sp.Symbol("sigma_val", real=True)
    tau_val = sp.Symbol("tau_val", real=True)
    s_complex = sigma_val + sp.I * tau_val

    fixed_diff = sp.simplify(gamma(s_complex) - s_complex)
    # gamma(sigma + i tau) = 1 - (sigma - i tau) = (1 - sigma) + i tau
    # gamma(s) - s = 1 - 2 sigma
    assert sp.re(fixed_diff) == 1 - 2 * sigma_val
    assert sp.im(fixed_diff) == 0
    # 1 - 2 sigma = 0 <===> sigma = 1/2
    assert sp.solve(sp.re(fixed_diff), sigma_val) == [sp.Rational(1, 2)]
    print("  [OK] Critical line fixed locus Fix(gamma) = {Re(s) = 1/2} verified")

    # 4. 2D Continuous Flow Lie Algebra
    t, lam = sp.symbols("t lambda", real=True)
    t1, t2, lam1, lam2 = sp.symbols("t1 t2 lam1 lam2", real=True)
    phi_H = lambda t_v, z: z + sp.I * t_v
    phi_S = lambda lam_v, z: z + lam_v

    assert sp.simplify(phi_H(t1 + t2, s) - phi_H(t1, phi_H(t2, s))) == 0
    assert sp.simplify(phi_S(lam1 + lam2, s) - phi_S(lam1, phi_S(lam2, s))) == 0
    assert sp.simplify(phi_H(t, phi_S(lam, s)) - phi_S(lam, phi_H(t, s))) == 0
    print("  [OK] 2D continuous flow group laws and commutativity [Phi_H, Phi_S] = 0 verified")

    # 5. Casimir Invariance & Critical Invariant Leaf
    assert sp.re(phi_H(t, s_complex)) == sigma_val
    s_crit = sp.Rational(1, 2) + sp.I * tau_val
    assert sp.re(phi_H(t, s_crit)) == sp.Rational(1, 2)
    print("  [OK] Casimir entropy conservation Re(Phi_H(s)) = Re(s) on critical leaf verified")

    print("=" * 72)
    print("NATIVE MATHLIB ZETA METRIPLECTIC FLOW VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
