#!/usr/bin/env python3
"""Klein Four-Group Semidirect Action on Zeta Flow & Height Character Verification.

Mirrors:
  * `InfoGeometry.Topology.ZetaCenteredCoordinateBridge`
  * `InfoGeometry.Topology.ZetaFlowKleinSemidirectBridge`

Verifies:
  1. Coordinate bijection: (u, tau) <-> 1/2 + u + i*tau
  2. V4 group laws and reflections:
       tau: (u, tau) -> (-u, -tau)   [s -> 1 - s]
       sigma: (u, tau) -> (u, -tau)  [s -> s*]
       gamma: (u, tau) -> (-u, tau)  [s -> 1 - s*]
  3. Critical line fixed locus: gamma(p) = p iff u = 0
  4. Height character:
       chi_h(id) = +1, chi_h(gamma) = +1, chi_h(sigma) = -1, chi_h(tau) = -1
       Homomorphism law: chi_h(g1 * g2) = chi_h(g1) * chi_h(g2)
  5. Semidirect flow conjugation:
       g . Phi_t(p) = Phi_{chi_h(g)*t}(g . p) for all g in V4
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
    print("KLEIN FOUR-GROUP SEMIDIRECT FLOW & HEIGHT CHARACTER CAS VERIFICATION")
    print("=" * 72)

    u, tau, t = sp.symbols("u tau t", real=True)
    p = (u, tau)

    # 1. Coordinate transformations
    to_complex = lambda pt: (sp.Rational(1, 2) + pt[0]) + sp.I * pt[1]
    of_complex = lambda s: (sp.re(s) - sp.Rational(1, 2), sp.im(s))

    s = to_complex(p)
    p_rec = of_complex(s)
    assert p_rec == p
    print("  [OK] ZetaFlowPoint <-> Complex bijection verified")

    # 2. V4 operations
    tau_act = lambda pt: (-pt[0], -pt[1])
    sigma_act = lambda pt: (pt[0], -pt[1])
    gamma_act = lambda pt: (-pt[0], pt[1])

    # Symmetries on C
    assert sp.simplify(to_complex(tau_act(p)) - (1 - s)) == 0
    assert sp.simplify(to_complex(sigma_act(p)) - sp.conjugate(s)) == 0
    assert sp.simplify(to_complex(gamma_act(p)) - (1 - sp.conjugate(s))) == 0
    print("  [OK] Complex plane reflection identifications verified")

    # Involutive and composition laws
    assert tau_act(tau_act(p)) == p
    assert sigma_act(sigma_act(p)) == p
    assert gamma_act(gamma_act(p)) == p
    assert gamma_act(p) == tau_act(sigma_act(p))
    assert gamma_act(p) == sigma_act(tau_act(p))
    print("  [OK] V4 involution and composition relations verified")

    # 3. Critical line fixed locus
    # gamma(p) = p <=> (-u, tau) = (u, tau) <=> u = 0
    assert gamma_act((0, tau)) == (0, tau)
    assert gamma_act((u, tau))[0] == -u  # equal to u iff u = 0
    print("  [OK] Critical line fixed locus gamma(p) = p <=> u = 0 verified")

    # 4. Vertical flow and semidirect action
    flow = lambda time, pt: (pt[0], pt[1] + time)

    # V4 group elements: (id, gamma, sigma, tau)
    V4 = {
        "id": (lambda pt: pt, +1),
        "gamma": (gamma_act, +1),
        "sigma": (sigma_act, -1),
        "tau": (tau_act, -1),
    }

    # 5. Semidirect flow conjugation: g . Phi_t(p) = Phi_{chi_h(g)*t}(g . p)
    for name, (act_g, chi_h) in V4.items():
        lhs = act_g(flow(t, p))
        rhs = flow(chi_h * t, act_g(p))
        assert lhs == rhs, f"Failed for {name}: {lhs} != {rhs}"
        print(f"  [OK] Semidirect conjugation for {name:5s} (chi_h = {chi_h:+d}): {lhs} == {rhs}")

    # Homomorphism law for chi_h
    # Multiplication table in V4 (Z2 x Z2)
    # id=0, gamma=1, sigma=2, tau=3
    mult_table = [
        ("id", "id", "id"),
        ("id", "gamma", "gamma"),
        ("id", "sigma", "sigma"),
        ("id", "tau", "tau"),
        ("gamma", "gamma", "id"),
        ("gamma", "sigma", "tau"),
        ("gamma", "tau", "sigma"),
        ("sigma", "sigma", "id"),
        ("sigma", "tau", "gamma"),
        ("tau", "tau", "id"),
    ]
    for g1, g2, g12 in mult_table:
        chi_1 = V4[g1][1]
        chi_2 = V4[g2][1]
        chi_12 = V4[g12][1]
        assert chi_1 * chi_2 == chi_12, f"Homomorphism failed: {g1} * {g2}"
    print("  [OK] Height character multiplicative homomorphism verified")

    print("=" * 72)
    print("KLEIN FOUR-GROUP SEMIDIRECT FLOW VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
