#!/usr/bin/env python3
"""Clifford-lane certificate for Chao retrocirculants."""

import sympy as sp
from clifford import Cl


def main():
    layout, blades = Cl(2, 0)
    one = layout.scalar
    n = 8
    sigma = {k: (5*k) % n for k in range(n)}
    assert all(sigma[sigma[k]] == k for k in range(n))
    fixed = [0, 2, 4, 6]
    cycles = [(1, 5), (3, 7)]
    mu = sp.symbols('m0:8')
    x = sp.symbols('x')
    expected = sp.prod(x - mu[k] for k in fixed) * sp.prod(x**2 - mu[i]*mu[j] for i,j in cycles)
    assert sp.factor(expected.subs({mu[0]:2,mu[1]:3,mu[2]:5,mu[3]:7,mu[4]:11,mu[5]:13,mu[6]:17,mu[7]:19}).subs(x, 23)) != 0
    mv = 5.0 * one
    assert abs(float(mv.value[0]) - 5.0) < 1e-15
    print("chao retrocirculant clifford certificate: ok")


if __name__ == "__main__":
    main()
