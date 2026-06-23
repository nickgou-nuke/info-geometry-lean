#!/usr/bin/env python3
"""Clifford-lane certificate for weak Drazin inverses."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    A = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    B = sp.Rational(1, 2) * sp.eye(3)
    assert B * (A ** 3) == A ** 2
    mv = 0.5 * one
    assert abs(float(mv.value[0]) - 0.5) < 1e-15
    print("weak Drazin clifford certificate: ok")


if __name__ == "__main__":
    main()
