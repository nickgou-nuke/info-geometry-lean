#!/usr/bin/env python3
"""Clifford-lane exact-rational witness for Gibson basic matrices."""

import sympy as sp
from clifford import Cl


def basic12(x):
    return sp.Matrix([[x, 1 - x, 0], [1 - x, x, 0], [0, 0, 1]])


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    x = sp.Rational(2, 3)
    M = basic12(x)
    ones = sp.Matrix([1, 1, 1])
    assert M * ones == ones
    assert M.T * ones == ones
    assert M.det() == 2 * x - 1
    scalar_mv = float(M.det()) * one
    assert abs(float(scalar_mv.value[0]) - sp.Rational(1, 3)) < 1e-15
    print("gibson basic doubly stochastic clifford certificate: ok")


if __name__ == "__main__":
    main()
