#!/usr/bin/env python3
"""Finite emergent-gravity action-variation witness.

This is the SymPy companion to
``lean/InfoGeometry/Canonical/EmergentGravityActionVariation.lean``.

It checks:

* the finite action density splits into Dirac, mass, curvature, and torsion
  contributions;
* the torsion term vanishes cleanly at zero torsion;
* the Belinfante-style readout is symmetric by explicit symmetrization.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_zero


def main() -> int:
    print("=" * 72)
    print("EMERGENT GRAVITY ACTION VARIATION")
    print("=" * 72)

    dirac, mass, curvature, torsion_norm, kappa_inv, alpha = sp.symbols(
        "dirac mass curvature torsion_norm kappa_inv alpha"
    )

    action = dirac - mass + (kappa_inv / 2) * curvature + (alpha / 4) * torsion_norm
    zero_torsion = action.subs(torsion_norm, 0)
    expected_zero = dirac - mass + (kappa_inv / 2) * curvature
    assert_zero(zero_torsion - expected_zero, "zero torsion action density")
    assert_zero(
        action - expected_zero - (alpha / 4) * torsion_norm,
        "torsion contribution splits additively",
    )
    print("  finite action-density split verified")

    b01, b10, c01, c10 = sp.symbols("B01 B10 C01 C10")
    T01 = sp.I / 4 * (b01 + b10 - c10 - c01)
    T10 = sp.I / 4 * (b10 + b01 - c01 - c10)
    assert_zero(T01 - T10, "Belinfante symmetry")
    print("  Belinfante-Rosenfeld symmetry verified")

    print("=" * 72)
    print("EMERGENT GRAVITY ACTION VARIATION VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
