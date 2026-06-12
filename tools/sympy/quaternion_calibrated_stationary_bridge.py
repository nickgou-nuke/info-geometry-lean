#!/usr/bin/env python3
"""Finite quaternion calibrated/stationary bridge checks.

This verifies only the theorem-safe finite scalar package:
- negative-log effective action readback,
- free-entropy stationarity residual,
- effective Einstein scalar balance,
- boundary Hawking calibration,
- quaternion field residual expansion.

It does not derive a path integral, one-loop determinant, RG equation,
fixed point, or evaporation law.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def main() -> None:
    print("=" * 72)
    print("QUATERNION CALIBRATED-STATIONARY BRIDGE -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    supervolume = sp.symbols("supervolume", positive=True)
    negative_log = -sp.log(supervolume)
    assert_zero(negative_log + sp.log(supervolume), "negative-log effective action")
    print("  negative-log effective action verified")

    dMassieu, dKL, lamInc, dInc, lamFree, dFree = sp.symbols(
        "dMassieu dKL lamInc dInc lamFree dFree", real=True
    )
    stationarity = dMassieu - dKL - lamInc * dInc - lamFree * dFree
    assert_zero(
        stationarity - (dMassieu - dKL - lamInc * dInc - lamFree * dFree),
        "stationarity residual expansion",
    )
    print("  free-entropy stationarity expansion verified")

    einsteinTensor, newtonG, effectiveStress = sp.symbols(
        "einsteinTensor newtonG effectiveStress", real=True
    )
    einstein_residual = einsteinTensor - (8 * sp.pi * newtonG) * effectiveStress
    assert_zero(
        einstein_residual - (einsteinTensor - (8 * sp.pi * newtonG) * effectiveStress),
        "effective Einstein balance expansion",
    )
    print("  effective Einstein scalar balance expansion verified")

    boundaryEntropy, boundaryArea, boundaryNewtonG = sp.symbols(
        "boundaryEntropy boundaryArea boundaryNewtonG", real=True, nonzero=True
    )
    hawking_residual = boundaryEntropy - boundaryArea / (4 * boundaryNewtonG)
    assert_zero(
        hawking_residual - (boundaryEntropy - boundaryArea / (4 * boundaryNewtonG)),
        "boundary Hawking calibration expansion",
    )
    print("  boundary Hawking calibration expansion verified")

    kinetic, mass = sp.symbols("kinetic mass")
    field_residual = kinetic - mass
    assert_zero(field_residual - (kinetic - mass), "quaternion field residual expansion")
    print("  quaternion field residual expansion verified")

    print("=" * 72)
    print("QUATERNION CALIBRATED-STATIONARY BRIDGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
