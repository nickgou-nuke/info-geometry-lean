#!/usr/bin/env python3
"""Exact-rational SymPy witnesses for Gibson basic doubly stochastic matrices."""

import sympy as sp


def basic12(x):
    return sp.Matrix([[x, 1 - x, 0], [1 - x, x, 0], [0, 0, 1]])


def main():
    x = sp.symbols('x')
    M = basic12(x)
    ones = sp.Matrix([1, 1, 1])
    assert sp.simplify(M * ones - ones) == sp.zeros(3, 1)
    assert sp.simplify(M.T * ones - ones) == sp.zeros(3, 1)
    assert sp.factor(M.det() - (2 * x - 1)) == 0

    A = basic12(sp.Rational(2, 3))
    B = basic12(sp.Rational(3, 5))
    P = A * B
    assert P * ones == ones
    assert P.T * ones == ones
    assert sp.factor(P.det() - A.det() * B.det()) == 0

    b = sp.symbols('b')
    obstruction = sp.Matrix([[1, 0, b], [0, 1 + b, b], [0, 0, 1]])
    assert sp.factor(obstruction.det() - (1 + b)) == 0
    print("gibson basic doubly stochastic SymPy certificate: ok")


if __name__ == "__main__":
    main()
