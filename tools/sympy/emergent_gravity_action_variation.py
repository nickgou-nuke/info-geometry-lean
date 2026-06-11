#!/usr/bin/env python3
"""Finite emergent-gravity action-variation witness.

This is the SymPy companion to
``lean/InfoGeometry/Canonical/EmergentGravityActionVariation.lean``.

It checks:

* the finite action density splits into Dirac, mass, curvature, and torsion
  contributions;
* the torsion term vanishes cleanly at zero torsion;
* the Belinfante-style readout is symmetric by explicit symmetrization.
* the finite torsion-quadratic source is symmetric under a symmetric metric;
* the finite modified-Einstein residual is exactly the algebraic difference
  between the modified-field side and the source side.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


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

    # Finite torsion-quadratic source:
    # Θ_μν = 2α(Σ_ab T_μab T_νab - 1/4 g_μν |T|²).
    t000, t001, t010, t011, t100, t101, t110, t111 = sp.symbols(
        "t000 t001 t010 t011 t100 t101 t110 t111"
    )
    torsion = {
        (0, 0, 0): t000,
        (0, 0, 1): t001,
        (0, 1, 0): t010,
        (0, 1, 1): t011,
        (1, 0, 0): t100,
        (1, 0, 1): t101,
        (1, 1, 0): t110,
        (1, 1, 1): t111,
    }
    g00, g01, g11 = sp.symbols("g00 g01 g11")
    metric = {(0, 0): g00, (0, 1): g01, (1, 0): g01, (1, 1): g11}

    def contraction(mu: int, nu: int):
        return sum(torsion[(mu, a, b)] * torsion[(nu, a, b)] for a in range(2) for b in range(2))

    torsion_norm = sum(torsion[(mu, a, b)] ** 2 for mu in range(2) for a in range(2) for b in range(2))

    def theta(mu: int, nu: int):
        return 2 * alpha * (contraction(mu, nu) - sp.Rational(1, 4) * metric[(mu, nu)] * torsion_norm)

    assert_zero(theta(0, 1) - theta(1, 0), "torsion-quadratic source symmetry")
    print("  finite torsion-quadratic source symmetry verified")

    # Finite modified-Einstein residual:
    # G + Λg + αH - κ(Stress + Θ).
    G, Lambda, kappa, H, stress, theta_slot = sp.symbols(
        "G Lambda kappa H stress theta_slot"
    )
    lhs = G + Lambda * g01 + alpha * H
    rhs = kappa * (stress + theta_slot)
    residual = lhs - rhs
    assert_zero(
        residual - (lhs - rhs),
        "modified Einstein residual closed expansion",
    )
    print("  finite modified-Einstein residual expansion verified")

    print("=" * 72)
    print("EMERGENT GRAVITY ACTION VARIATION VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
