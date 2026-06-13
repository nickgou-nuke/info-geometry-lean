#!/usr/bin/env python3
"""Finite/truncated generating-function witness for Horadam 2^k-ions.

For G_n(t)=sum_{i=0}^n W_i t^i and W_{i+2}=pW_{i+1}+qW_i:

  (1-p t-q t^2)G_n(t)
    = W_0 + (W_1-pW_0)t - W_{n+1}t^{n+1} - q W_n t^{n+2}.

This is the theorem-safe finite version of the paper's ordinary generating
function.  It has explicit boundary terms and makes no infinite-series or
convergence claim.  The coordinate/2^k-ion lift is checked componentwise.
"""

from __future__ import annotations

import sympy as sp


def horadam_values(a, b, p, q, count: int) -> list[sp.Expr]:
    vals = [sp.sympify(a), sp.sympify(b)]
    for i in range(count - 2):
        vals.append(sp.expand(p * vals[i + 1] + q * vals[i]))
    return vals[:count]


def main() -> None:
    a, b, p, q, t = sp.Integer(2), sp.Integer(3), sp.Integer(5), sp.Integer(-2), sp.symbols("t")
    vals = horadam_values(a, b, p, q, 40)

    for n in range(12):
        G = sum(vals[i] * t**i for i in range(n + 1))
        lhs = sp.expand((1 - p * t - q * t**2) * G)
        rhs = sp.expand(vals[0] + (vals[1] - p * vals[0]) * t - vals[n + 1] * t ** (n + 1) - q * vals[n] * t ** (n + 2))
        assert lhs == rhs

    # Coordinate lift: shift the scalar sequence by s.
    N = 8
    for s in range(N):
        for n in range(8):
            G = sum(vals[i + s] * t**i for i in range(n + 1))
            lhs = sp.expand((1 - p * t - q * t**2) * G)
            rhs = sp.expand(vals[s] + (vals[s + 1] - p * vals[s]) * t - vals[n + 1 + s] * t ** (n + 1) - q * vals[n + s] * t ** (n + 2))
            assert lhs == rhs

    print("HORADAM_ION_GENERATING_SLICE_FINITE_OK")
    print("scope: finite truncated generating-function identity with boundary terms only; no infinite-series convergence")


if __name__ == "__main__":
    main()
