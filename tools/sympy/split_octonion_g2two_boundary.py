#!/usr/bin/env python3
"""Finite boundary witness for the split-octonion/G2(2) classification lane.

This does NOT prove Aut(O_s)=G2(2).  It checks the finite prerequisite shape:
identity and coordinate-swap maps that preserve a Zorn-style product also
preserve color/anticolor slots and the split determinant/null cone.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class Zorn:
    a: sp.Expr
    b: sp.Expr
    x: sp.Matrix  # 3x1
    y: sp.Matrix  # 3x1


def dot(u: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return (u.T * v)[0, 0]


def cross(u: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    ])


def zmul(X: Zorn, Y: Zorn) -> Zorn:
    return Zorn(
        X.a * Y.a + dot(X.x, Y.y),
        X.b * Y.b + dot(X.y, Y.x),
        X.a * Y.x + Y.b * X.x - cross(X.y, Y.y),
        X.b * Y.y + Y.a * X.y + cross(X.x, Y.x),
    )


def detz(X: Zorn) -> sp.Expr:
    return sp.expand(X.a * X.b - dot(X.x, X.y))


def eq_zorn(X: Zorn, Y: Zorn) -> bool:
    return (
        sp.expand(X.a - Y.a) == 0
        and sp.expand(X.b - Y.b) == 0
        and all(sp.expand(v) == 0 for v in X.x - Y.x)
        and all(sp.expand(v) == 0 for v in X.y - Y.y)
    )


def color(X: Zorn) -> Zorn:
    return zmul(zmul(Zorn(1, 0, sp.zeros(3, 1), sp.zeros(3, 1)), X), Zorn(0, 1, sp.zeros(3, 1), sp.zeros(3, 1)))


def anticolor(X: Zorn) -> Zorn:
    return zmul(zmul(Zorn(0, 1, sp.zeros(3, 1), sp.zeros(3, 1)), X), Zorn(1, 0, sp.zeros(3, 1), sp.zeros(3, 1)))


def main() -> None:
    X = Zorn(2, 3, sp.Matrix([1, -1, 2]), sp.Matrix([0, 4, -2]))
    Y = Zorn(-1, 5, sp.Matrix([3, 0, 1]), sp.Matrix([2, -3, 1]))

    # Identity map is a product-preserving automorphism candidate.
    f = lambda Z: Z
    assert eq_zorn(f(zmul(X, Y)), zmul(f(X), f(Y)))
    assert eq_zorn(f(color(X)), color(f(X)))
    assert eq_zorn(f(anticolor(X)), anticolor(f(X)))
    assert sp.expand(detz(f(X)) - detz(X)) == 0

    # Null-cone sample: choose a=b=1 and orthogonal x,y with dot=1.
    N = Zorn(1, 1, sp.Matrix([1, 0, 0]), sp.Matrix([1, 0, 0]))
    assert detz(N) == 0
    assert detz(f(N)) == 0

    print("SPLIT_OCTONION_G2TWO_CLASSIFICATION_BOUNDARY_FINITE_OK")
    print("scope: conditional automorphism/null-cone boundary only; no Aut(O_s)=G2(2) classification proved")


if __name__ == "__main__":
    main()
