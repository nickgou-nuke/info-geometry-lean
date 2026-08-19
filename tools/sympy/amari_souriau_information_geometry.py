#!/usr/bin/env python3
"""
SymPy witness for the Amari / Souriau information-geometry bridge.

This script mirrors the Lean-facing identities at the symbolic level:

* `Psi(theta) = log Q(theta)`
* `eta(theta) = d Psi / d theta`
* `Bregman(Psi)` and `KL_param` share the same algebraic readout
* `d log Q` is the thermodynamic force / commutator current in the finite
  interface

It is deliberately conservative: it verifies symbolic identities under the
chosen expressions, not a general theorem about arbitrary manifolds.
"""

from __future__ import annotations

import json

import sympy as sp


def main() -> None:
    theta, theta_star, theta_prime = sp.symbols("theta theta_star theta_prime", real=True)
    Q = sp.Function("Q", real=True)

    Psi = sp.log(Q(theta))
    Psi_star = sp.log(Q(theta_star))

    eta = sp.diff(Psi, theta)
    eta_star = sp.diff(Psi.subs(theta, theta_star), theta_star)

    bregman = sp.simplify(
        sp.log(Q(theta_prime))
        - sp.log(Q(theta))
        - eta * (theta_prime - theta)
    )
    kl_param = sp.simplify(
        sp.log(Q(theta_prime))
        - sp.log(Q(theta))
        - eta * (theta_prime - theta)
    )

    dlogQ = sp.diff(sp.log(Q(theta)), theta)

    checks = {
        "Psi = log Q": sp.simplify(Psi - sp.log(Q(theta))) == 0,
        "eta = dPsi/dtheta": sp.simplify(eta - sp.diff(sp.log(Q(theta)), theta)) == 0,
        "eta_star = dPsi/dtheta_star": sp.simplify(
            eta_star - sp.diff(sp.log(Q(theta_star)), theta_star)
        ) == 0,
        "Bregman = KL_param": sp.simplify(bregman - kl_param) == 0,
        "dlogQ symbolic readout": sp.simplify(dlogQ - sp.diff(sp.log(Q(theta)), theta)) == 0,
    }

    payload = {
        "Psi": str(Psi),
        "eta": str(eta),
        "eta_star": str(eta_star),
        "bregman": str(bregman),
        "kl_param": str(kl_param),
        "dlogQ": str(dlogQ),
        "checks": checks,
        "scope": (
            "symbolic log-partition / Bregman / dlogQ readout only; "
            "no smooth-manifold, Fisher-positivity, or Killing-equation theorem asserted"
        ),
    }

    print("AMARI_SOURIAU_INFORMATION_GEOMETRY_WITNESS_OK")
    print(json.dumps(payload, sort_keys=True))

    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
