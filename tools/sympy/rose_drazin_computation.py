#!/usr/bin/env python3
"""Exact-rational SymPy witnesses for Rose's Drazin-inverse computation."""

import sympy as sp


def main():
    x = sp.symbols('x')

    # Example 1: modulo x^2 + 5x + 1, x^-3 = -24x - 115.
    f1 = x**2 + 5*x + 1
    p1 = -24*x - 115
    assert sp.rem(x**3 * p1 - 1, f1, domain=sp.QQ) == 0

    # A concrete matrix with characteristic polynomial λ^2(λ^2+5λ+1).
    C1 = sp.Matrix([[0, -1], [1, -5]])
    A1 = sp.diag(0, 0, C1)
    D1 = A1**2 * (-24*A1 - 115*sp.eye(4))
    assert A1**3 * D1 == A1**2
    assert D1 * A1 == A1 * D1

    # Example 2: modulo x^4+x^3+x^2+x+1, x*x^4 = 1.
    f2 = x**4 + x**3 + x**2 + x + 1
    assert sp.rem(x * x**4 - 1, f2, domain=sp.QQ) == 0

    # Souriau-Frame style traces on a 2x2 companion block.
    char = C1.charpoly(x).as_expr()
    assert sp.factor(char - f1) == 0
    print("rose Drazin computation SymPy certificate: ok")


if __name__ == "__main__":
    main()
