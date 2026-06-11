#!/usr/bin/env python3
"""
SymPy witness for the primitive Cuntz exactness bridge.

This is a computational twin of the Lean algebraic surfaces in:

* InfoGeometry.Canonical.PrimitiveCuntzIsometry
* InfoGeometry.Canonical.PrimitiveCuntzCohomology
* InfoGeometry.Canonical.UHFCohomologyColimit

It is not a proof replacement.  Lean remains authoritative.  The script expands
noncommutative words and applies the same explicit Cuntz rewrite rules used in
Lean:

    SL* SL = 1,  SR* SR = 1,
    SL SL* + SR SR* = 1,
    SL* SR = 0,  SR* SL = 0.
"""

from __future__ import annotations

import sympy as sp


SL = sp.Symbol("S_L", commutative=False)
SR = sp.Symbol("S_R", commutative=False)
SLs = sp.Symbol("S_L_star", commutative=False)
SRs = sp.Symbol("S_R_star", commutative=False)
X = sp.Symbol("X", commutative=False)
I = sp.Symbol("I", commutative=False)
ZERO = sp.Integer(0)

PL = SL * SLs
PR = SR * SRs


def reduce_cuntz(
    expr: sp.Expr,
    assume_x_projection: bool = False,
    use_orthogonality: bool = True,
) -> sp.Expr:
    """Normalize the finite words that appear in the Cuntz bridge witnesses."""
    e = sp.expand(expr)

    rules = [
        (SLs * SL, I),
        (SRs * SR, I),
        (SL * I * SLs, SL * SLs),
        (SR * I * SRs, SR * SRs),
        (SLs * I * SR, SLs * SR),
        (SRs * I * SL, SRs * SL),
        (I * SLs * SR, SLs * SR),
        (SLs * SR * I, SLs * SR),
        (I * SRs * SL, SRs * SL),
        (SRs * SL * I, SRs * SL),
        (SL * X * I * X * SLs, SL * X * X * SLs),
        (SR * X * I * X * SRs, SR * X * X * SRs),
        (PL + PR, I),
        (I * X, X),
        (X * I, X),
        (SL * SLs * X + SR * SRs * X, X),
    ]
    if use_orthogonality:
        rules.extend([
            (SLs * SR, ZERO),
            (SRs * SL, ZERO),
        ])
    if assume_x_projection:
        rules.extend([
            (X * X, X),
            (SL * X * X * SLs, SL * X * SLs),
            (SR * X * X * SRs, SR * X * SRs),
        ])

    changed = True
    while changed:
        old = e
        for lhs, rhs in rules:
            e = e.subs(lhs, rhs)
        e = sp.expand(e)
        changed = e != old
    return e


def main() -> None:
    print("--- SymPy Twin: Primitive Cuntz Exactness Bridge ---")

    # Orthogonality derivation readout:
    # SL* (PL + PR) SR = SL* SR, while expansion gives SL*SR + SL*SR.
    # Additive cancellation yields SL*SR = 0; Lean proves this algebraically.
    lhs_parent = reduce_cuntz(SLs * I * SR, use_orthogonality=False)
    rhs_expanded = reduce_cuntz(SLs * PL * SR + SLs * PR * SR, use_orthogonality=False)
    print(f"orthogonality cancellation equation: {lhs_parent} = {rhs_expanded}")
    print("Lean cancellation theorem concludes: S_L_star*S_R = 0")

    boundary = SL * SRs
    boundary_star = SR * SLs
    boundary_sq = reduce_cuntz(boundary * boundary)
    print(f"boundary^2 reduced: {boundary_sq}")
    assert boundary_sq == 0

    laplacian = boundary * boundary_star + boundary_star * boundary
    laplacian_reduced = reduce_cuntz(laplacian)
    print(f"laplacian reduced: {laplacian_reduced}")
    assert laplacian_reduced == I

    phi_x = SL * X * SLs + SR * X * SRs
    phi_x_sq_reduced = reduce_cuntz(phi_x * phi_x, assume_x_projection=True)
    print(f"Phi(X)^2 reduced under X^2=X: {phi_x_sq_reduced}")
    assert phi_x_sq_reduced == phi_x

    phi_one = reduce_cuntz(SL * I * SLs + SR * I * SRs)
    print(f"Phi(1) reduced: {phi_one}")
    assert phi_one == I

    print("[SUCCESS] SymPy witness matches the Lean Cuntz/UHF exactness bridge.")


if __name__ == "__main__":
    main()
