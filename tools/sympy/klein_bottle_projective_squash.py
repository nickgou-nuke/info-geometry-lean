#!/usr/bin/env python3
"""Exact-rational SymPy audit for projective Klein compactification formulas."""

from __future__ import annotations

import sympy as sp


def projectively_equal(A: sp.Matrix, B: sp.Matrix) -> bool:
    return A == B or A == -B


def main() -> None:
    I2 = sp.eye(2)
    minus_I2 = -I2
    twist_a = sp.Matrix([[1, 0], [0, -1]])
    parabolic_b = sp.Matrix([[1, 1], [0, 1]])
    parabolic_b_inv = sp.Matrix([[1, -1], [0, 1]])
    mobius_s = sp.Matrix([[0, -1], [1, 0]])
    t = sp.Symbol("t")

    assert projectively_equal(I2, minus_I2)
    assert minus_I2 * minus_I2 == I2
    assert twist_a * twist_a == I2
    assert parabolic_b * parabolic_b_inv == I2
    assert parabolic_b_inv * parabolic_b == I2
    assert twist_a * parabolic_b * twist_a == parabolic_b_inv
    assert twist_a * parabolic_b * twist_a * parabolic_b == I2
    assert mobius_s * sp.Matrix([t, 1]) == sp.Matrix([-1, t])
    assert projectively_equal(mobius_s * mobius_s, I2)

    print("projective Klein compactification SymPy audit: ok")


if __name__ == "__main__":
    main()
