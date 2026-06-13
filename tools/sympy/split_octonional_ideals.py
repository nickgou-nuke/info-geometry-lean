#!/usr/bin/env python3
"""Exact finite projector/ideal absorption verifier for the split-octonion lane.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionalIdeals.lean

Scope: finite 32x32 quadrant projectors inherited from the Cole-Fury block
surface.  It verifies idempotence, absorption `(R P) P = R P` for representative
ambient block generators, and horizon incidence laws.  It does not implement full
split-octonion multiplication, nonassociativity, or G2(2) automorphism theory.
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
G0 = LL * UR - UR * LL
NEG = -I32


def representative_ambient_generators() -> list[sp.Matrix]:
    return [I32, NEG, UL, LR, UR, LL, G0, UR + LL, UL - LR]


def verify_projector_absorption() -> None:
    for P in [UL, LR]:
        assert P * P == P
        for R in representative_ambient_generators():
            assert (R * P) * P == R * P
            assert P * (P * R) == P * R


def verify_horizon_incidence() -> None:
    assert UR * UL == Z32
    assert UL * UR == UR
    assert UR * LR == UR
    assert LR * UR == Z32
    assert LL * UL == LL
    assert UL * LL == Z32
    assert LL * LR == Z32
    assert LR * LL == LL


def verify_corner_closure() -> None:
    assert UL + LR == I32
    assert UL * LR == Z32
    assert LR * UL == Z32
    assert UR * UR == Z32
    assert LL * LL == Z32
    assert UR * LL == UL
    assert LL * UR == LR
    assert G0 == -UL + LR
    assert G0 * G0 == I32


def main() -> None:
    verify_projector_absorption()
    verify_horizon_incidence()
    verify_corner_closure()
    print("OK split_octonional_ideals: finite quadrant projector absorption verified")
    print("OK idempotents: UL^2=UL, LR^2=LR; absorption (R*P)*P=R*P for representative block generators")
    print("OK horizon incidence and corner closure against Cole-Fury 32D block laws")
    print("scope: finite matrix projector law; no full split-octonion/G2(2)/particle theorem claimed")


if __name__ == "__main__":
    main()
