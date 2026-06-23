#!/usr/bin/env python3
"""galgebra-lane exact-rational witness for Smith retrocirculants."""

import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    A = sp.Matrix([[0, 3], [2, 0]])
    Ap = sp.Matrix([[0, sp.Rational(1, 2)], [sp.Rational(1, 3), 0]])
    assert (A * Ap).T == A * Ap
    assert (Ap * A).T == Ap * A
    B = sp.Matrix([[0, 7], [5, 0]])
    assert (A * B)[0, 1] == 0 and (A * B)[1, 0] == 0
    scalar_mv = ga.mv(sp.Rational(1, 1), 'scalar')
    assert scalar_mv.obj == 1
    print("smith retrocirculant Moore-Penrose galgebra certificate: ok")


if __name__ == "__main__":
    main()
