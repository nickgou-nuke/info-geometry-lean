#!/usr/bin/env python3
"""GAlgebra-lane audit for the projective Klein formula packet."""

from __future__ import annotations

import sympy as sp
from galgebra.ga import Ga


def projectively_equal(a: sp.Matrix, b: sp.Matrix) -> bool:
    return a == b or a == -b


def main() -> None:
    ga = Ga("e1 e2", g=[1, 1])
    e1, e2 = ga.mv_basis
    v = 3 * e1 + 5 * e2
    reflected = (-e2 * v * e2).simplify()
    assert str((reflected - (3 * e1 - 5 * e2)).simplify()) == "0"

    i2 = sp.eye(2)
    twist_a = sp.Matrix([[1, 0], [0, -1]])
    parabolic_b = sp.Matrix([[1, 1], [0, 1]])
    parabolic_b_inv = sp.Matrix([[1, -1], [0, 1]])
    mobius_s = sp.Matrix([[0, -1], [1, 0]])
    assert twist_a * parabolic_b * twist_a == parabolic_b_inv
    assert twist_a * parabolic_b * twist_a * parabolic_b == i2
    assert projectively_equal(mobius_s * mobius_s, i2)

    print("projective Klein compactification galgebra audit: ok")


if __name__ == "__main__":
    main()
