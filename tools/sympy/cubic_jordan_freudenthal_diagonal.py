#!/usr/bin/env python3
"""Diagonal Freudenthal identity for the cubic Jordan/Albert diagonal subalgebra.

For X=(a,b,c), X#=(bc,ac,ab), N(X)=abc, hence (X#)#=N(X)X.
"""

import sympy as sp


def adjoint_diag(x):
    a, b, c = x
    return sp.Matrix([b*c, a*c, a*b])


def norm_diag(x):
    a, b, c = x
    return a*b*c


def main():
    a, b, c = sp.symbols('a b c')
    x = sp.Matrix([a, b, c])
    lhs = adjoint_diag(adjoint_diag(x))
    rhs = norm_diag(x) * x
    assert sp.simplify(lhs - rhs) == sp.zeros(3, 1)
    print('diagonal cubic Jordan Freudenthal identity ok')


if __name__ == '__main__':
    main()
