#!/usr/bin/env python3
"""Exact SymPy witnesses for `O55V4KleinBottleFinite.lean`.

Checks only finite coordinate identities:
- central sign and two hyperbolic pair-reflections preserve the split pairing;
- the two reflections are involutive and commute, giving a V4 shadow;
- the affine Klein-bottle relation r t(a) r = t(-a).

Not a construction of O(5,5), Pin(5,5), CCC, or orbit classification.
"""

from __future__ import annotations

import sympy as sp


def pair(x: sp.Matrix, y: sp.Matrix) -> sp.Expr:
    return sum(x[i] * y[i + 5] + x[i + 5] * y[i] for i in range(5))


def diag_with_flips(*idx: int) -> sp.Matrix:
    m = sp.eye(10)
    for i in idx:
        m[i, i] = -1
    return m


def trans0(x: sp.Matrix, a: sp.Expr) -> sp.Matrix:
    y = sp.Matrix(x)
    y[0] += a
    return y


def aff_refl0(x: sp.Matrix) -> sp.Matrix:
    y = sp.Matrix(x)
    y[0] = -y[0]
    return y


def main() -> None:
    xs = sp.symbols("x0:10")
    ys = sp.symbols("y0:10")
    a = sp.symbols("a")
    x = sp.Matrix(xs)
    y = sp.Matrix(ys)

    neg = -sp.eye(10)
    r0 = diag_with_flips(0, 5)
    r1 = diag_with_flips(1, 6)

    for name, m in [("neg", neg), ("r0", r0), ("r1", r1), ("r0r1", r0 * r1)]:
        assert sp.simplify(pair(m * x, m * y) - pair(x, y)) == 0, name
        assert m * m == sp.eye(10), name
    assert r0 * r1 == r1 * r0

    lhs = aff_refl0(trans0(aff_refl0(x), a))
    rhs = trans0(x, -a)
    assert sp.simplify(lhs - rhs) == sp.zeros(10, 1)

    print("O55_V4_NEG_PAIRING_OK")
    print("O55_V4_REFLECTIONS_OK")
    print("O55_V4_COMMUTING_INVOLUTIONS_OK")
    print("O55_KLEIN_BOTTLE_AFFINE_RELATION_OK")


if __name__ == "__main__":
    main()
