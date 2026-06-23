#!/usr/bin/env python3
"""Finite witness for `OnShellResidueBCFWBridge.lean`.

This checks only local algebra/bookkeeping:

* the local model `∮ dz/z = 2*pi*I`;
* a three-pole residue balance can be represented by choosing the third
  residue as the negative of the first two;
* the illustrative diagram bookkeeping `220 -> 1` has difference `219`.

It does not prove a residue theorem on a compactification, BCFW recursion, an
amplituhedron volume formula, or a scattering-amplitude theorem.
"""

from __future__ import annotations

import json

import sympy as sp


def verify_local_dlog_residue() -> dict[str, str | bool]:
    t, radius = sp.symbols("t radius", positive=True, real=True)
    z = radius * sp.exp(sp.I * t)
    integral = sp.simplify(sp.integrate((1 / z) * sp.diff(z, t), (t, 0, 2 * sp.pi)))
    return {
        "integral": str(integral),
        "equals_2pi_i": bool(sp.simplify(integral - 2 * sp.pi * sp.I) == 0),
    }


def verify_three_pole_balance() -> dict[str, str | bool]:
    r12, r23 = sp.symbols("r12 r23")
    r31 = -(r12 + r23)
    balance = sp.simplify(r12 + r23 + r31)
    return {
        "r31": str(r31),
        "balance": str(balance),
        "is_zero": bool(balance == 0),
    }


def verify_diagram_bookkeeping() -> dict[str, int | bool]:
    diagram_count = 220
    carrier_count = 1
    return {
        "diagram_count": diagram_count,
        "carrier_count": carrier_count,
        "carrier_lt_diagram": carrier_count < diagram_count,
        "difference": diagram_count - carrier_count,
        "difference_eq_219": diagram_count - carrier_count == 219,
    }


def main() -> None:
    checks = {
        "local_dlog_residue": verify_local_dlog_residue(),
        "three_pole_balance": verify_three_pole_balance(),
        "diagram_bookkeeping": verify_diagram_bookkeeping(),
        "non_claims": [
            "no BCFW recursion theorem asserted",
            "no amplituhedron volume theorem asserted",
            "no scattering-amplitude theorem asserted",
        ],
    }

    assert checks["local_dlog_residue"]["equals_2pi_i"]
    assert checks["three_pole_balance"]["is_zero"]
    assert checks["diagram_bookkeeping"]["carrier_lt_diagram"]
    assert checks["diagram_bookkeeping"]["difference_eq_219"]

    print("ON_SHELL_RESIDUE_BCFW_WITNESS_OK")
    print(json.dumps(checks, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
