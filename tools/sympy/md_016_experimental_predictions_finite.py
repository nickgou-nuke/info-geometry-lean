#!/usr/bin/env python3
"""Finite witness for MD 016 experimental-prediction algebra.

Mirrors `InfoGeometry.Physics.MD016ExperimentalPredictionsFinite`.

Verified theorem-safe content only:
* scalar cross-section modification factor algebra;
* finite linearized triality-breaking angle shadow;
* frequency-quadratic gravitational-wave speed shadow;
* entropy-scaling equation-of-state arithmetic;
* two-component flat cosmology ratio sum.

No collider-amplitude, neutrino-mixing, CP-violation, gravitational-wave PDE,
Lorentz-violation, dark-energy, Planck-parameter, or detectability theorem is
claimed.
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
    print("MD 016 FINITE EXPERIMENTAL-PREDICTION ALGEBRA")
    print("=" * 72)

    sigma_sm, alpha, E, Lambda, F = sp.symbols("sigma_sm alpha E Lambda F", nonzero=True)
    factor = 1 + alpha * E**2 / Lambda**2 * F
    sigma = sigma_sm * factor
    assert_zero(factor.subs(alpha, 0) - 1, "zero alpha cross-section factor")
    assert_zero(factor.subs(E, 0) - 1, "zero energy cross-section factor")
    assert_zero(sigma - sigma_sm - sigma_sm * (alpha * E**2 / Lambda**2 * F), "modified cross-section excess")
    print("cross-section scalar modification algebra: OK")

    baseline, sensitivity, delta = sp.symbols("baseline sensitivity delta")
    angle = baseline + sensitivity * delta
    assert_zero(angle.subs(delta, 0) - baseline, "zero triality-breaking angle shift")
    assert_zero(angle - baseline - sensitivity * delta, "linear triality-breaking difference")
    print("linear triality-breaking shadow: OK")

    c, beta, f, f0, gamma = sp.symbols("c beta f f0 gamma", nonzero=True)
    v = c * (1 - beta * (f / f0) ** 2)
    assert_zero(v.subs(f, 0) - c, "GW speed zero frequency")
    assert_zero(v.subs(f, f0) - c * (1 - beta), "GW speed reference frequency")
    assert_zero(c - v - c * beta * (f / f0) ** 2, "GW speed deficit")
    beta_coeff = 6 * sp.pi**2 * gamma * f0**2
    assert_zero(beta_coeff.subs(gamma, 0), "GW beta zero gamma")
    print("frequency-quadratic GW speed shadow: OK")

    eps = sp.symbols("eps")
    w = -1 + eps / 3
    assert_zero(w.subs(eps, 0) + 1, "dark-energy EOS zero epsilon")
    assert_zero(w.subs(eps, sp.Rational(6, 100)) + sp.Rational(98, 100), "dark-energy EOS sample")
    print("entropy equation-of-state arithmetic: OK")

    gam = sp.symbols("gam", nonzero=True)
    omega_lambda = 1 / (1 + gam)
    omega_m = gam / (1 + gam)
    assert_zero(omega_lambda + omega_m - 1, "flat two-component cosmology ratio")
    print("flat cosmology ratio algebra: OK")

    print("=" * 72)
    print("MD 016 FINITE EXPERIMENTAL-PREDICTION ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
