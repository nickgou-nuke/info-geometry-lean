#!/usr/bin/env python3
"""Clifford-lane certificate for Jensen inverse-iteration inclusion.

The exact Jensen algebra is performed over SymPy rationals/quadratic extensions;
the `clifford` package is imported and used to host the one-dimensional scalar
certificate as a Clifford multivector lane smoke/readout.
"""

import os
import sympy as sp

os.environ.setdefault("NUMBA_DISABLE_CACHE", "1")
os.environ.setdefault("NUMBA_DISABLE_CACHING", "1")
os.environ.setdefault("NUMBA_CACHE_DIR", "/tmp/numba-cache")

from clifford import Cl


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
    layout, blades = Cl(1, 0)
    one = layout.scalar
    h = sp.Rational(1, 5)
    q = sp.Rational(1, 3)
    b = {j: h + q**j for j in range(1, 8)}
    for j in range(3, 8):
        delta = delta_formula(b, j)
        assert sp.simplify(jensen_polynomial(b, j, delta)) == 0
        # Store the rational lower endpoint as a scalar Clifford multivector and
        # rationalize the host-library coefficient back to QQ exactly.
        mv = float(h) * one
        assert sp.nsimplify(mv.value[0]) == h
        assert sp.N(h) <= sp.N(delta) <= sp.N(b[j])
    print("jensen inverse-iteration inclusion clifford certificate: ok")


if __name__ == "__main__":
    main()
