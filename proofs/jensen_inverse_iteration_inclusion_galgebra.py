#!/usr/bin/env python3
"""galgebra-lane certificate for Jensen inverse-iteration inclusion.

Exact Jensen algebra is SymPy-rational.  `galgebra` hosts the scalar certificate
inside a one-dimensional geometric algebra environment.
"""

import sympy as sp
from galgebra.ga import Ga


def jensen_polynomial(b, j, z):
    return (-(b[j - 1] - b[j]) * z**2
            + b[j - 1] * (b[j - 2] - b[j]) * z
            - b[j - 1] * b[j] * (b[j - 2] - b[j - 1]))


def delta_formula(b, j):
    rad = ((b[j - 2] - b[j])**2
           - 4 * (b[j - 1] - b[j]) * (b[j - 2] - b[j - 1]) * (b[j] / b[j - 1]))
    return sp.simplify(b[j - 1] * ((b[j - 2] - b[j]) - sp.sqrt(rad)) /
                       (2 * (b[j - 1] - b[j])))


def main():
    x = sp.symbols('x')
    ga = Ga('e', g=[1], coords=[x])
    h = sp.Rational(1, 5)
    q = sp.Rational(1, 3)
    b = {j: h + q**j for j in range(1, 8)}
    scalar_mv = ga.mv(h, 'scalar')
    assert scalar_mv.obj == h
    for j in range(3, 8):
        delta = delta_formula(b, j)
        assert sp.simplify(jensen_polynomial(b, j, delta)) == 0
        assert sp.N(h) <= sp.N(delta) <= sp.N(b[j])
    print("jensen inverse-iteration inclusion galgebra certificate: ok")


if __name__ == "__main__":
    main()
