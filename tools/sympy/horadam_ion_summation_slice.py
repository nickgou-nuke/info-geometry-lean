#!/usr/bin/env python3
"""Finite Horadam 2^k-ion summation slice witness.

This mirrors `InfoGeometry.Arithmetic.HoradamIonSummationSlice`.
It checks the cleared-denominator finite geometric-sum identity for the Binet
core C_i = A alpha^i - B beta^i:

  (1-alpha)(1-beta) sum_{i=0}^n C_i
    = A(1-beta)(1-alpha^{n+1}) - B(1-alpha)(1-beta^{n+1}).

No infinite generating function, convergence theorem, or Cayley-Dickson product
is asserted.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    A, B, alpha, beta = sp.symbols("A B alpha beta")
    for n in range(10):
        lhs = (1 - alpha) * (1 - beta) * sum(A * alpha**i - B * beta**i for i in range(n + 1))
        rhs = A * (1 - beta) * (1 - alpha ** (n + 1)) - B * (1 - alpha) * (1 - beta ** (n + 1))
        assert sp.expand(lhs - rhs) == 0

    # Coordinate lift sample.
    N = 8
    for n in range(5):
        for s in range(N):
            lhs = (1 - alpha) * (1 - beta) * sum(A * alpha ** (i + s) - B * beta ** (i + s) for i in range(n + 1))
            rhs = A * (1 - beta) * alpha**s * (1 - alpha ** (n + 1)) - B * (1 - alpha) * beta**s * (1 - beta ** (n + 1))
            assert sp.expand(lhs - rhs) == 0

    print("HORADAM_ION_SUMMATION_SLICE_FINITE_OK")
    print("scope: finite cleared-denominator Binet partial sums only; no analytic generating-function or Cayley-Dickson theorem")


if __name__ == "__main__":
    main()
