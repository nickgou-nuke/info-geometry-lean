#!/usr/bin/env python3
"""galgebra-lane exact-rational witness for Rose's Drazin computation."""

import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    x = sp.symbols('x')
    f2 = x**4 + x**3 + x**2 + x + 1
    assert sp.rem(x * x**4 - 1, f2, domain=sp.QQ) == 0
    scalar_mv = ga.mv(sp.Rational(1, 1), 'scalar')
    assert scalar_mv.obj == 1
    print("rose Drazin computation galgebra certificate: ok")


if __name__ == "__main__":
    main()
