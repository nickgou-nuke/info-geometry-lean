#!/usr/bin/env python3
"""Exact algebra checks for arXiv:1608.03679v4.

This script mirrors the theorem-safe Lean corridor in
InfoGeometry.Arithmetic.Arxiv160803679BenderHamiltonian.  It checks only the
finite symbolic algebra from the paper:

* E = i(2z-1) inverts to z = (1-iE)/2;
* z = 1/2 + i t gives real E = -2t;
* psi_z(0) = -zeta(z) makes psi_z(0)=0 equivalent to zeta(z)=0;
* commuting x,p reduce xp+px to 2xp.

It deliberately does not claim self-adjointness, spectral completeness, or RH.
"""

import sympy as sp


def main() -> None:
    z, E, t, x, p, zeta = sp.symbols("z E t x p zeta")
    I = sp.I

    spectral_z = (1 - I * E) / 2
    eigen_E = I * (2 * z - 1)
    assert sp.simplify(spectral_z.subs(E, eigen_E) - z) == 0

    critical_z = sp.Rational(1, 2) + I * t
    critical_E = sp.simplify(I * (2 * critical_z - 1))
    assert critical_E == -2 * t

    psi0 = -zeta
    assert sp.solve(sp.Eq(psi0, 0), zeta) == [0]

    berry_keating_shadow = x * p + p * x
    assert sp.simplify(berry_keating_shadow - 2 * x * p) == 0

    print("arXiv:1608.03679 Bender Hamiltonian algebra checks passed.")


if __name__ == "__main__":
    main()
