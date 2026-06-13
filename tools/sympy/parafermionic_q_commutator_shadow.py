#!/usr/bin/env python3
"""Finite 2x2 q-commutator shadow for the Peirce-Witt lane.

This verifies only the elementary matrix identities

    U D - q D U = E_plus - q E_minus
    U D - D U = H
    U D + D U = I

for the canonical nilpotent 2x2 slots.  It does not assert Cuntz closure,
Yang-Baxter/braid coherence, wallpaper forcing, or any global automorphism
classification.
"""
from __future__ import annotations

import sympy as sp


def main() -> None:
    q = sp.Symbol("q")

    e_plus = sp.Matrix([[1, 0], [0, 0]])
    e_minus = sp.Matrix([[0, 0], [0, 1]])
    identity = e_plus + e_minus
    h = e_plus - e_minus

    up = sp.Matrix([[0, 1], [0, 0]])
    down = sp.Matrix([[0, 0], [1, 0]])

    assert up * up == sp.zeros(2)
    assert down * down == sp.zeros(2)
    assert up * down == e_plus
    assert down * up == e_minus
    assert up * down - q * down * up == e_plus - q * e_minus
    assert up * down - down * up == h
    assert up * down + down * up == identity

    print("PARAFERMIONIC_Q_COMMUTATOR_SHADOW_OK")
    print("scope: finite 2x2 Peirce-Witt/q-commutator shadow only")


if __name__ == "__main__":
    main()
