#!/usr/bin/env python3
"""Exact-rational SymPy certificate for Campbell--Meyer weak Drazin inverses."""

import sympy as sp


def main():
    A = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    B_min = sp.Matrix([[sp.Rational(1, 2), 0, 0], [0, 0, 0], [0, 0, 0]])
    B_poly = sp.Rational(1, 2) * sp.eye(3)
    k = 2

    assert B_min * (A ** (k + 1)) == A ** k
    assert B_poly * (A ** (k + 1)) == A ** k
    assert A * B_poly == B_poly * A

    x = sp.symbols('x')
    char = A.charpoly(x).as_expr()
    assert sp.factor(char - x**2 * (x - 2)) == 0
    # Theorem 4 polynomial inverse from p(x)=x^2(-2+x): -1/c0*c1 I = 1/2 I.
    assert B_poly == sp.Rational(1, 2) * sp.eye(3)
    print("weak Drazin SymPy certificate: ok")


if __name__ == "__main__":
    main()
