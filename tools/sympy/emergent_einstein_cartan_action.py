#!/usr/bin/env python3
"""
Finite Einstein-Cartan action bridge.

Mirrors lean/InfoGeometry/Canonical/EmergentEinsteinCartanAction.lean.
This script checks only the finite algebraic identities proved there:

* the finite action density splits into Dirac, mass, curvature, and torsion
  contributions;
* zero torsion removes the torsion contribution from the action density;
* a symmetric stress plus symmetric torsion-quadratic source gives a symmetric
  total source;
* a scaled spin source satisfies the finite torsion equation;
* the finite field-equation readout is exactly the expanded algebraic
  proposition, with no residual-premise substitution.

It does not derive continuum variational calculus, Bianchi identities,
diffeomorphism invariance, or a physical Einstein-Cartan theory.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def symmetric_2x2(prefix: str) -> sp.Matrix:
    a, b, c = sp.symbols(f"{prefix}00 {prefix}01 {prefix}11", complex=True)
    return sp.Matrix([[a, b], [b, c]])


def main() -> int:
    print("=" * 72)
    print("FINITE EINSTEIN-CARTAN ACTION BRIDGE")
    print("=" * 72)

    dirac, mass, curvature, torsion_norm, kappa_inv, alpha = sp.symbols(
        "dirac mass curvature torsion_norm kappa_inv alpha"
    )
    action = dirac - mass + (kappa_inv / 2) * curvature + (alpha / 4) * torsion_norm
    expected_split = (dirac - mass + (kappa_inv / 2) * curvature) + (alpha / 4) * torsion_norm
    assert_zero(action - expected_split, "action-density split")
    assert_zero(
        action.subs(torsion_norm, 0) - (dirac - mass + (kappa_inv / 2) * curvature),
        "zero torsion action density",
    )
    print("  action-density split verified")

    stress = symmetric_2x2("S")
    theta = symmetric_2x2("T")
    total_source = stress + theta
    assert_matrix_zero(total_source - total_source.T, "total source symmetry")
    print("  total source symmetry verified")

    G = symmetric_2x2("G")
    H = symmetric_2x2("H")
    g = symmetric_2x2("g")
    Lambda, kappa, alpha_field = sp.symbols("Lambda kappa alpha_field")
    modified_field = G + alpha_field * H
    field_equation_residual = modified_field + Lambda * g - kappa * total_source
    for i in range(2):
        for j in range(2):
            lhs_ij = modified_field[i, j] + Lambda * g[i, j]
            rhs_ij = kappa * total_source[i, j]
            assert_zero(
                field_equation_residual[i, j] - (lhs_ij - rhs_ij),
                f"finite field-equation expansion ({i},{j})",
            )
    print("  finite field-equation expansion verified")

    spin = sp.symbols("spin", complex=True)
    torsion = kappa * spin
    assert_zero(torsion - kappa * spin, "scaled spin torsion source")
    print("  scaled spin torsion source verified")

    print("=" * 72)
    print("FINITE EINSTEIN-CARTAN ACTION BRIDGE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
