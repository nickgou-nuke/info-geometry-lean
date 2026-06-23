#!/usr/bin/env python3
"""Exact-rational SymPy audit for the projective Klein formula packet."""

from __future__ import annotations

import sympy as sp


def projectively_equal(a: sp.Matrix, b: sp.Matrix) -> bool:
    return a == b or a == -b


def main() -> None:
    i2 = sp.eye(2)
    minus_i2 = -i2
    twist_a = sp.Matrix([[1, 0], [0, -1]])
    parabolic_b = sp.Matrix([[1, 1], [0, 1]])
    parabolic_b_inv = sp.Matrix([[1, -1], [0, 1]])
    mobius_s = sp.Matrix([[0, -1], [1, 0]])
    t = sp.Symbol("t")

    assert projectively_equal(i2, minus_i2)
    assert minus_i2 * minus_i2 == i2
    assert twist_a * twist_a == i2
    assert parabolic_b * parabolic_b_inv == i2
    assert parabolic_b_inv * parabolic_b == i2
    assert twist_a * parabolic_b * twist_a == parabolic_b_inv
    assert twist_a * parabolic_b * twist_a * parabolic_b == i2
    assert mobius_s * sp.Matrix([t, 1]) == sp.Matrix([-1, t])
    assert projectively_equal(mobius_s * mobius_s, i2)

    print("projective Klein compactification SymPy audit: ok")


if __name__ == "__main__":
    main()
