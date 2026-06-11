#!/usr/bin/env python3
"""Finite witness for the Evans-style harmonic trap transition table.

The Lean owner is `InfoGeometry.Canonical.EvansHarmonicTrap`.

This script checks only the finite deterministic local rules:
    +0 -> 0+
    0- -> -0
    +- -> -+
and verifies that the three-site trap `(-, 0, +)` is fixed under left and
right adjacent-pair updates.

No thermodynamic limit, KMS/BEC statement, zeta theorem, or RH consequence is
claimed here.
"""

from __future__ import annotations


EXACT = "+"
COEXACT = "-"
HARMONIC = "0"


def transition(left: str, right: str) -> tuple[str, str]:
    if (left, right) == (EXACT, HARMONIC):
        return (HARMONIC, EXACT)
    if (left, right) == (HARMONIC, COEXACT):
        return (COEXACT, HARMONIC)
    if (left, right) == (EXACT, COEXACT):
        return (COEXACT, EXACT)
    return (left, right)


def update_left(triple: tuple[str, str, str]) -> tuple[str, str, str]:
    left, center, right = triple
    new_left, new_center = transition(left, center)
    return (new_left, new_center, right)


def update_right(triple: tuple[str, str, str]) -> tuple[str, str, str]:
    left, center, right = triple
    new_center, new_right = transition(center, right)
    return (left, new_center, new_right)


def main() -> None:
    print("=== EVANS 1D LATTICE HARMONIC TRAP WITNESS ===")

    assert transition(EXACT, HARMONIC) == (HARMONIC, EXACT)
    assert transition(HARMONIC, COEXACT) == (COEXACT, HARMONIC)
    assert transition(EXACT, COEXACT) == (COEXACT, EXACT)
    print("[1] active local transition rules verified")

    assert transition(COEXACT, HARMONIC) == (COEXACT, HARMONIC)
    assert transition(HARMONIC, EXACT) == (HARMONIC, EXACT)
    print("[2] trap boundary pairs are fixed")

    trap = (COEXACT, HARMONIC, EXACT)
    assert update_left(trap) == trap
    assert update_right(trap) == trap
    print("[3] three-site harmonic trap is pairwise invariant")

    print("=== SUCCESS: FINITE HARMONIC TRAP TABLE VERIFIED ===")


if __name__ == "__main__":
    main()
