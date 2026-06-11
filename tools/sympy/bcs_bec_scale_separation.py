#!/usr/bin/env python3
"""Finite algebra checks for the BCS--BEC scale-separation skeleton.

The source paper is a physics review; the Lean module formalizes only the
real-order skeleton: separated pair-formation and condensation temperatures
give a nonempty preformed-pair interval.
"""

from __future__ import annotations

import sympy as sp


def verify_midpoint_window() -> None:
    tc, tstar = sp.symbols("T_c T_star")
    midpoint = (tc + tstar) / 2
    separation = tstar - tc

    left_gap = sp.simplify(midpoint - tc)
    right_gap = sp.simplify(tstar - midpoint)

    assert sp.simplify(left_gap - separation / 2) == 0
    assert sp.simplify(right_gap - separation / 2) == 0
    print("[scales] midpoint splits the pair-formation/condensation gap in half")


def verify_strict_bcs_exclusion() -> None:
    tc, tstar = sp.symbols("T_c T_star")
    locked_gap = sp.simplify((tstar - tc).subs(tstar, tc))

    assert locked_gap == 0
    print("[scales] strict BCS locking collapses the crossover gap")


def verify_chemical_potential_sign_disjointness() -> None:
    samples = [sp.Rational(1, 3), sp.Rational(5, 2)]
    for mu in samples:
        assert mu > 0
        assert not (mu < 0)
        assert -mu < 0
        assert not (-mu > 0)
    print("[chemical-potential] positive and negative side readouts are disjoint")


def main() -> None:
    print("=== BCS--BEC Scale-Separation Witness ===")
    verify_midpoint_window()
    verify_strict_bcs_exclusion()
    verify_chemical_potential_sign_disjointness()
    print("=== SUCCESS ===")


if __name__ == "__main__":
    main()
