#!/usr/bin/env python3
"""Exact matrix verifier for the projective center quotient {+I,-I}.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/ProjectiveCenterQuotient.lean

Scope: finite matrix facts for the central signed identities on the 32-component
real spinor carrier.  This verifies the projective identification A ~ -A for a
representative Cl(5,5) spinor generator set without claiming a full topological
construction of Pin(5,5)/{±1}.
"""
from __future__ import annotations

import sympy as sp

I2 = sp.eye(2)
A2 = sp.Matrix([[0, 1], [1, 0]])
B2 = sp.Matrix([[0, 1], [-1, 0]])
C2 = sp.Matrix([[1, 0], [0, -1]])
I32 = sp.eye(32)
NEG_I32 = -I32
Z32 = sp.zeros(32)


def kron_all(parts: list[sp.Matrix]) -> sp.Matrix:
    out = parts[0]
    for part in parts[1:]:
        out = sp.kronecker_product(out, part)
    return sp.Matrix(out)


def build_gammas() -> list[sp.Matrix]:
    gammas: list[sp.Matrix] = []
    for r in range(5):
        prefix = [C2] * r
        suffix = [I2] * (4 - r)
        gammas.append(kron_all(prefix + [A2] + suffix))
    for r in range(5):
        prefix = [C2] * r
        suffix = [I2] * (4 - r)
        gammas.append(kron_all(prefix + [B2] + suffix))
    return gammas


def verify_center_for_generators(gammas: list[sp.Matrix]) -> None:
    for G in gammas:
        assert I32 * G == G * I32
        assert NEG_I32 * G == G * NEG_I32
        assert NEG_I32 * G == -G
        assert G * NEG_I32 == -G


def verify_center_group() -> None:
    assert I32 * I32 == I32
    assert NEG_I32 * NEG_I32 == I32
    assert I32 * NEG_I32 == NEG_I32
    assert NEG_I32 * I32 == NEG_I32


def verify_projective_equivalence(gammas: list[sp.Matrix]) -> None:
    # A representative quotient check: multiplying by the nontrivial central
    # element twice returns the same representative.
    for G in gammas:
        assert NEG_I32 * (NEG_I32 * G) == G
        assert (G * NEG_I32) * NEG_I32 == G
        assert NEG_I32 * G == G * NEG_I32
        assert (NEG_I32 * G) + G == Z32


def main() -> None:
    gammas = build_gammas()
    verify_center_group()
    verify_center_for_generators(gammas)
    verify_projective_equivalence(gammas)
    print("OK projective_center_quotient: {+I32,-I32} central involution verified")
    print("OK commutes with all ten exact Cl(5,5) spinor generators")
    print("OK projective representative check: (-I)*((-I)*G)=G and (-I)*G=G*(-I)=-G")
    print("scope: finite signed-identity center quotient; no topological PO/Pin quotient claimed")


if __name__ == "__main__":
    main()
