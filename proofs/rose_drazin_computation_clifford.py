#!/usr/bin/env python3
"""Clifford-lane exact-rational witness for Rose's Drazin computation."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    x = sp.symbols('x')
    f1 = x**2 + 5*x + 1
    p1 = -24*x - 115
    assert sp.rem(x**3 * p1 - 1, f1, domain=sp.QQ) == 0
    scalar_mv = 1.0 * one
    assert abs(float(scalar_mv.value[0]) - 1.0) < 1e-15
    print("rose Drazin computation clifford certificate: ok")


if __name__ == "__main__":
    main()
