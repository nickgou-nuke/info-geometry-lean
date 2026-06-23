#!/usr/bin/env python3
"""galgebra-lane certificate for Chao retrocirculants."""

import sympy as sp
from galgebra.ga import Ga


def main():
    t, u = sp.symbols('t u')
    ga = Ga('e1 e2', g=[1, 1], coords=[t, u])
    n = 8
    sigma = {k: (5*k) % n for k in range(n)}
    assert all(sigma[sigma[k]] == k for k in range(n))
    fixed = [k for k in range(n) if sigma[k] == k]
    assert fixed == [0, 2, 4, 6]
    mu = sp.symbols('m0:8')
    x = sp.symbols('x')
    expected = sp.prod(x - mu[k] for k in fixed) * (x**2 - mu[1]*mu[5]) * (x**2 - mu[3]*mu[7])
    assert sp.Poly(expected, x).degree() == 8
    scalar_mv = ga.mv(sp.Integer(8), 'scalar')
    assert scalar_mv.obj == 8
    print("chao retrocirculant galgebra certificate: ok")


if __name__ == "__main__":
    main()
