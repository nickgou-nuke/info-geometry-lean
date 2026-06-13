#!/usr/bin/env python3
"""Exact 32-dimensional Cole-Fury ideal block verifier.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/ColeFuryIdeals.lean

Scope: finite 2x2 block matrix laws on the 32-component spinor carrier with
16x16 quadrant blocks.  This verifies the upper-right and lower-left nilpotent
horizon blocks and their diagonal commutator closure.  It does not claim a full
physical electron/positron classification theorem.
"""
from __future__ import annotations

import sympy as sp

I16 = sp.eye(16)
Z16 = sp.zeros(16)
I32 = sp.eye(32)
Z32 = sp.zeros(32)


def block2(a: sp.Matrix, b: sp.Matrix, c: sp.Matrix, d: sp.Matrix) -> sp.Matrix:
    return sp.Matrix.vstack(sp.Matrix.hstack(a, b), sp.Matrix.hstack(c, d))


UL = block2(I16, Z16, Z16, Z16)
UR = block2(Z16, I16, Z16, Z16)
LL = block2(Z16, Z16, I16, Z16)
LR = block2(Z16, Z16, Z16, I16)

partial = UR
partial_dag = LL
g0_core = partial_dag * partial - partial * partial_dag
expected_g0 = block2(-I16, Z16, Z16, I16)


def verify_projector_quadrants() -> None:
    assert UL * UL == UL
    assert LR * LR == LR
    assert UL * LR == Z32
    assert LR * UL == Z32
    assert UL + LR == I32


def verify_nilpotent_horizons() -> None:
    assert partial * partial == Z32
    assert partial_dag * partial_dag == Z32
    assert partial * partial_dag == UL
    assert partial_dag * partial == LR
    assert partial * partial_dag + partial_dag * partial == I32


def verify_commutator_closure() -> None:
    assert g0_core == expected_g0
    assert sp.trace(g0_core) == 0
    assert g0_core * g0_core == I32
    assert g0_core * partial - partial * g0_core == -2 * partial
    assert g0_core * partial_dag - partial_dag * g0_core == 2 * partial_dag


def verify_central_projective_balance() -> None:
    neg = -I32
    assert neg * partial == partial * neg
    assert neg * partial_dag == partial_dag * neg
    assert neg * g0_core == g0_core * neg
    assert neg * neg == I32


def main() -> None:
    verify_projector_quadrants()
    verify_nilpotent_horizons()
    verify_commutator_closure()
    verify_central_projective_balance()
    print("OK cole_fury_ideals: 32D quadrant projectors and nilpotent horizons verified")
    print("OK laws: partial^2=0, partial_dag^2=0, partial*partial_dag=UL, partial_dag*partial=LR")
    print("OK commutator: [g_-1,g_+1]=diag(-I16,+I16), trace 0, grading action ±2")
    print("scope: finite quadrant block laws; no physical charge-classification theorem claimed")


if __name__ == "__main__":
    main()
