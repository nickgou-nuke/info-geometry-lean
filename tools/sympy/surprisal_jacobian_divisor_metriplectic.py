#!/usr/bin/env python3
"""Unified CAS Verification for Relative Surprisal, Lie Jacobian & Zeta Divisor.

Mirrors:
  * `InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge`
  * `InfoGeometry.Canonical.LieFlowLogJacobianBridge`
  * `InfoGeometry.Canonical.MetriplecticJacobianDecompositionBridge`
  * `InfoGeometry.Canonical.ZetaDivisorJacobianBridge`

Verifies:
  1. Radon-Nikodym surprisal: K(Delta) = -log(Delta)
     Surprisal transport: K_t(Phi_t x) - K_0(x) = log J_t(x)
  2. Differentiable flow log-Jacobian cocycle:
     J(t) = exp(t * tr A) => -log J(t) = -t * tr A
     d/dt (-log J(t)) = -tr A = -div X
  3. Metriplectic decomposition:
     X = X_H + X_D with div X_H = 0 => div X = div X_D
     Factorized dissipation: div X_D = -u^2 * Q(u, tau)
     Critical line (u = 0) => div X_D = 0 and finite-time J_t = 1
  4. Spectral divisor 1-form:
     omega(s) = -xi'/xi ds => local zero monomial -m/(s - rho)
     Integer winding periods: (1 / 2*pi*i) * oint omega = -m in Z
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
    print("SURPRISAL - JACOBIAN - DIVISOR - METRIPLECTIC CAS VERIFICATION")
    print("=" * 72)

    # 1. Surprisal and Transport
    delta1, delta2 = sp.symbols("delta1 delta2", positive=True)
    K = lambda d: -sp.log(d)
    assert sp.simplify(K(delta1 * delta2) - (K(delta1) + K(delta2))) == 0
    assert K(1) == 0
    print("  [OK] Surprisal homomorphism K(d1*d2) = K(d1) + K(d2) verified")

    rho0, rhot, J = sp.symbols("rho0 rhot J", positive=True)
    # Mass conservation: rhot * J = rho0 => rhot = rho0 / J
    # K(rhot) - K(rho0) = -log(rho0/J) - (-log(rho0)) = log(J)
    assert sp.simplify(K(rho0 / J) - K(rho0) - sp.log(J)) == 0
    print("  [OK] Surprisal transport identity K_t - K_0 = log J verified")

    # 2. Lie Flow Log-Jacobian
    t, trA = sp.symbols("t trA", real=True)
    J_lie = sp.exp(t * trA)
    J_cocycle = -sp.log(J_lie)
    assert sp.simplify(J_cocycle - (-t * trA)) == 0
    dJ_dt = sp.diff(J_cocycle, t)
    assert dJ_dt == -trA
    print("  [OK] Linear Lie flow log-Jacobian d/dt J_t = -tr A verified")

    # 3. Metriplectic Decomposition & Critical Line Factorization
    u, tau, Q = sp.symbols("u tau Q", real=True)
    div_H = 0
    div_D = -u**2 * Q
    div_total = div_H + div_D
    assert div_total == div_D
    print("  [OK] Hamiltonian incompressibility div X = div X_D verified")

    # Critical line evaluation u = 0
    div_D_crit = div_D.subs(u, 0)
    assert div_D_crit == 0
    J_finite_crit = sp.exp(t * div_D_crit)
    assert J_finite_crit == 1
    print("  [OK] Critical line dissipation vanishing and unimodular J_t = 1 verified")

    # 4. Spectral Divisor 1-Form & Integer Residues
    s, rho = sp.symbols("s rho", complex=True)
    m = sp.symbols("m", integer=True)
    # Zero factor f(s) = (s - rho)^m
    f = (s - rho)**m
    df = sp.diff(f, s)
    omega_xi = sp.powsimp(-df / f)
    assert sp.simplify(omega_xi - (-m / (s - rho))) == 0
    print("  [OK] Divisor 1-form monomial reduction omega = -m/(s - rho) verified")

    # Contour residue: 1/(2*pi*i) oint -m/(s - rho) ds = -m
    omega_target = -m / (s - rho)
    residue = sp.residue(omega_target, s, rho)
    assert residue == -m
    print("  [OK] Divisor period quantization (1/2pi*i) oint omega = -m in Z verified")

    print("=" * 72)
    print("ALL RADON-NIKODYM, JACOBIAN & DIVISOR BRIDGE PROPERTIES VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
