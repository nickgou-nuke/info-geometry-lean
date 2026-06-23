#!/usr/bin/env python3
"""galgebra-lane certificate for weak Drazin inverses."""

import sympy as sp
from galgebra.ga import Ga


def main():
    x = sp.symbols('x')
    ga = Ga('e', g=[1], coords=[x])
    A = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    B = sp.Rational(1, 2) * sp.eye(3)
    assert B * (A ** 3) == A ** 2
    scalar_mv = ga.mv(sp.Rational(1, 2), 'scalar')
    assert scalar_mv.obj == sp.Rational(1, 2)
    print("weak Drazin galgebra certificate: ok")


if __name__ == "__main__":
    main()
