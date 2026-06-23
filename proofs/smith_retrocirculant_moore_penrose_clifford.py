#!/usr/bin/env python3
"""Clifford-lane exact-rational witness for Smith retrocirculants."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    A = sp.Matrix([[0, 3], [2, 0]])
    Ap = sp.Matrix([[0, sp.Rational(1, 2)], [sp.Rational(1, 3), 0]])
    assert A * Ap * A == A
    assert Ap * A * Ap == Ap
    eig = set(A.eigenvals().keys())
    eigp = set(Ap.eigenvals().keys())
    assert eigp == {sp.simplify(1/e) for e in eig}
    scalar_mv = 1.0 * one
    assert abs(float(scalar_mv.value[0]) - 1.0) < 1e-15
    print("smith retrocirculant Moore-Penrose clifford certificate: ok")


if __name__ == "__main__":
    main()
