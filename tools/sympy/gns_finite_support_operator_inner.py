#!/usr/bin/env python3
"""Finite-support GNS bounded-operator inner-product laws.

Mirrors `GNSFiniteSupportOperatorInner.lean`:
- π(a)Ω = restrict(a)
- <Ω,π(a)Ω> = ω(a)
- <π(a)x,y> = <x,π(a*)y>
- π(a*a)=π(a*)π(a)
"""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def diag_op(a, mask):
    return sp.diag(*active(a, mask))


def inner(x, y):
    return sum(sp.conjugate(xi) * yi for xi, yi in zip(x, y))


def involution(a):
    return [sp.conjugate(ai) for ai in a]


def main():
    n = 4
    mask = (True, False, True, True)
    m = sum(mask)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    x = sp.Matrix(sp.symbols(f"x0:{m}", complex=True))
    y = sp.Matrix(sp.symbols(f"y0:{m}", complex=True))
    Omega = sp.Matrix([1] * m)

    A = diag_op(a, mask)
    Astar = diag_op(involution(a), mask)
    pos = diag_op([sp.conjugate(ai) * ai for ai in a], mask)

    assert sp.simplify(A * Omega - sp.Matrix(active(a, mask))) == sp.zeros(m, 1)
    assert sp.simplify(inner(Omega, A * Omega) - sum(active(a, mask))) == 0
    assert sp.simplify(inner(A * x, y) - inner(x, Astar * y)) == 0
    assert sp.simplify(pos - Astar * A) == sp.zeros(m, m)
    assert sp.simplify(inner(Omega, pos * Omega) - sum(active([sp.conjugate(ai) * ai for ai in a], mask))) == 0

    print("finite-support GNS operator inner-product checks ok")


if __name__ == "__main__":
    main()
