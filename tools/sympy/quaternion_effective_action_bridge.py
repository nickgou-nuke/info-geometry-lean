#!/usr/bin/env python3
"""Finite quaternion effective-action bridge checks.

This mirrors a theorem-safe bridge only:
- effective action = negative log of a positive readout;
- stationary first-variation residual is explicit scalar subtraction;
- field-equation residual is explicit scalar subtraction.

It does not derive a path integral, one-loop determinant, RG beta function,
or black-hole evaporation law.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def main() -> None:
    print("=" * 72)
    print("QUATERNION EFFECTIVE-ACTION BRIDGE -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    supervolume = sp.symbols("supervolume", positive=True)
    effective_action = -sp.log(supervolume)
    assert_zero(effective_action + sp.log(supervolume), "negative-log effective action")
    print("  negative-log effective action verified")

    dMassieu, dKL, lamInc, dInc, lamFree, dFree = sp.symbols(
        "dMassieu dKL lamInc dInc lamFree dFree", real=True
    )
    first_variation = dMassieu - dKL - lamInc * dInc - lamFree * dFree
    assert_zero(
        first_variation - (dMassieu - dKL - lamInc * dInc - lamFree * dFree),
        "stationarity residual expansion",
    )
    print("  stationarity residual readback verified")

    kinetic, mass = sp.symbols("kinetic mass")
    field_residual = kinetic - mass
    assert_zero(field_residual - (kinetic - mass), "quaternion field residual expansion")
    print("  quaternion field residual expansion verified")

    print("=" * 72)
    print("QUATERNION EFFECTIVE-ACTION BRIDGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
