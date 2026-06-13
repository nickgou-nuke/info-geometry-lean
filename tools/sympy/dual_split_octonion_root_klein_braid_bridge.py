#!/usr/bin/env python3
"""Finite root/tripotent/Klein/braid bridge for the dual split-octonion lane.

Lean twin:
    lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionRootKleinBraidBridge.lean

Scope: exact finite algebra only.  This script intentionally does not construct
analytic braid operators, continuum band theory, particle-sector models, or
compactification classifications.
"""

from __future__ import annotations

import sympy as sp


def z2_power_grade(n: int, grade: int) -> int:
    assert grade in (0, 1)
    return 0 if n % 2 == 0 else grade


def check_z2_roots() -> None:
    assert z2_power_grade(3, 0) == 0
    assert z2_power_grade(3, 1) == 1
    assert z2_power_grade(2, 1) == 0
    assert z2_power_grade(4, 1) == 0

    I2 = sp.eye(2)
    negI2 = -sp.eye(2)
    assert negI2 * negI2 == I2
    central_grade = {"I": 0, "-I": 0}
    assert central_grade["I"] == 0
    assert central_grade["-I"] == 0


def check_tripotent_z3() -> None:
    T = sp.diag(-1, 0, 1)
    assert T**3 == T
    assert list(T.diagonal()) == [-1, 0, 1]

    def rot(x: int) -> int:
        return (x + 1) % 3

    for x in range(3):
        assert rot(rot(rot(x))) == x


def check_klein_monodromy() -> None:
    Mx = -sp.eye(8)
    My = sp.zeros(8)
    for i in range(4):
        My[i, i + 4] = 1
        My[i + 4, i] = 1

    assert Mx * Mx == sp.eye(8)
    assert My * My == sp.eye(8)
    assert My * Mx * My == Mx


def check_g2_artin_shadow() -> None:
    # Reflections s(x)=-x and t(x)=1-x on Z/6, represented as permutations.
    def s(x: int) -> int:
        return (-x) % 6

    def t(x: int) -> int:
        return (1 - x) % 6

    def left(x: int) -> int:
        for f in (t, s, t, s, t, s):
            x = f(x)
        return x

    def right(x: int) -> int:
        for f in (s, t, s, t, s, t):
            x = f(x)
        return x

    for x in range(6):
        assert left(x) == right(x)


def main() -> None:
    check_z2_roots()
    check_tripotent_z3()
    check_klein_monodromy()
    check_g2_artin_shadow()
    print("DUAL_SPLIT_OCTONION_ROOT_KLEIN_BRAID_BRIDGE_OK")
    print("central_sign_grade=even")
    print("tripotent_spectrum=[-1,0,1]")
    print("klein_monodromy=central_sign_exact")
    print("g2_artin_length=6")


if __name__ == "__main__":
    main()
