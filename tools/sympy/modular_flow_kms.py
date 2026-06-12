#!/usr/bin/env python3
"""
SymPy witness for the finite KMS modular-flow algebra corridor.

This mirrors `InfoGeometry.Holography.ModularFlowKMS`:
if two generators transform by the same central unitary phase, their chiral
crossing `X Y*` is fixed.  This is a finite algebraic witness only; it is not a
proof of unbounded Tomita--Takesaki theory or KMS analyticity.
"""

from __future__ import annotations

import sympy as sp

from primitive_cuntz_exactness_bridge import reduce_cuntz, SL, SR, SLs, SRs, X


phase = sp.Symbol("phase", commutative=True)
phase_star = sp.Symbol("phase_star", commutative=True)
Y = sp.Symbol("Y", commutative=False)
Ys = sp.Symbol("Y_star", commutative=False)
Xs = sp.Symbol("X_star", commutative=False)


def reduce_phase(expr: sp.Expr) -> sp.Expr:
    """Reduce central unitary phase factors."""
    e = sp.expand(expr)
    changed = True
    while changed:
        old = e
        e = sp.expand(e.subs(phase * phase_star, 1).subs(phase_star * phase, 1))
        changed = e != old
    return e


def modular_flow(expr: sp.Expr) -> sp.Expr:
    """Finite symbolic modular flow on the displayed generators."""
    return expr.subs({
        SL: phase * SL,
        SR: phase * SR,
        SLs: SLs * phase_star,
        SRs: SRs * phase_star,
        X: phase * X,
        Y: phase * Y,
        Xs: Xs * phase_star,
        Ys: Ys * phase_star,
    })


def main() -> None:
    print("--- SymPy Twin: Modular Flow KMS Invariance ---")

    # Generic crossing invariance under a common unitary phase.
    generic_crossing = X * Ys
    flowed_generic = reduce_phase(modular_flow(generic_crossing))
    print(f"Generic crossing reduced: {flowed_generic}")
    assert flowed_generic == generic_crossing

    # Cuntz horizon and reverse crossing.
    horizon = SL * SRs
    reverse_horizon = SR * SLs
    flowed_horizon = reduce_phase(modular_flow(horizon))
    flowed_reverse = reduce_phase(modular_flow(reverse_horizon))
    print(f"Original Horizon: {horizon}")
    print(f"Time-Evolved Horizon (reduced): {flowed_horizon}")
    print(f"Reverse Horizon (reduced): {flowed_reverse}")
    assert flowed_horizon == horizon
    assert flowed_reverse == reverse_horizon

    # Higgs/modular-conjugation crossing as the sum of both fixed crossings.
    higgs = horizon + reverse_horizon
    flowed_higgs = reduce_phase(modular_flow(higgs))
    print(f"Original Higgs Mass: {higgs}")
    print(f"Time-Evolved Higgs Mass (reduced): {flowed_higgs}")
    assert flowed_higgs == higgs

    # Nilpotence is stable because the horizon itself is fixed.
    flowed_horizon_sq = reduce_cuntz(reduce_phase(modular_flow(horizon)) * reduce_phase(modular_flow(horizon)))
    print(f"Time-evolved horizon square reduced: {flowed_horizon_sq}")
    assert flowed_horizon_sq == 0

    print("[SUCCESS] finite modular-flow crossing invariants match the Lean proofs.")


if __name__ == "__main__":
    main()
