#!/usr/bin/env python3
"""galgebra-lane exact-rational witness for Gibson basic matrices."""

import sympy as sp
from galgebra.ga import Ga


def basic12(x):
    return sp.Matrix([[x, 1 - x, 0], [1 - x, x, 0], [0, 0, 1]])


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    x = sp.Rational(3, 5)
    M = basic12(x)
    ones = sp.Matrix([1, 1, 1])
    assert M * ones == ones
    assert M.T * ones == ones
    assert M.det() == 2 * x - 1
    scalar_mv = ga.mv(M.det(), 'scalar')
    assert scalar_mv.obj == sp.Rational(1, 5)
    print("gibson basic doubly stochastic galgebra certificate: ok")


if __name__ == "__main__":
    main()
