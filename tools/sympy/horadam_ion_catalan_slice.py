#!/usr/bin/env python3
"""Finite Catalan/Cassini-style Binet identity witness for Horadam 2^k-ions.

This mirrors `InfoGeometry.Arithmetic.HoradamIonCatalanSlice`.
For the commutative Binet core C_n = A alpha^n - B beta^n it checks:

  C_m C_{m+2r} - C_{m+r}^2
    = - A B (alpha beta)^m (alpha^r - beta^r)^2.

This is a theorem-safe coordinate shadow of the paper's Catalan/Cassini family.
It does not formalize noncommutative Cayley-Dickson multiplication.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    A, B, alpha, beta = sp.symbols("A B alpha beta")
    for m in range(6):
        for r in range(6):
            C = lambda n: A * alpha**n - B * beta**n
            lhs = sp.expand(C(m) * C(m + 2 * r) - C(m + r) ** 2)
            rhs = sp.expand(-A * B * (alpha * beta) ** m * (alpha**r - beta**r) ** 2)
            assert sp.expand(lhs - rhs) == 0

    # Coordinate lift sample: shift by s.
    N = 8
    for s in range(N):
        for m in range(4):
            for r in range(4):
                C = lambda n: A * alpha**n - B * beta**n
                lhs = sp.expand(C(m + s) * C(m + s + 2 * r) - C(m + s + r) ** 2)
                rhs = sp.expand(-A * B * (alpha * beta) ** (m + s) * (alpha**r - beta**r) ** 2)
                assert sp.expand(lhs - rhs) == 0

    print("HORADAM_ION_CATALAN_SLICE_FINITE_OK")
    print("scope: commutative Binet Catalan/Cassini coordinate identity only; no Cayley-Dickson product theorem")


if __name__ == "__main__":
    main()
