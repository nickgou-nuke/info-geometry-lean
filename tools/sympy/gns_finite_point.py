#!/usr/bin/env python3
"""Finite n-point algebraic GNS mirror.

This mirrors `GNSFinite.lean` for a concrete symbolic finite dimension.
Algebra: C^n with pointwise operations.
Cyclic vector: Ω=(1,...,1).
Inner product: <x,y> = Σ conjugate(x_i) y_i.
Representation: π(a)x = a*x pointwise.
"""

import sympy as sp


def inner(xs, ys):
    return sum(sp.conjugate(x) * y for x, y in zip(xs, ys))


def involution(xs):
    return [sp.conjugate(x) for x in xs]


def add(xs, ys):
    return [x + y for x, y in zip(xs, ys)]


def mul(xs, ys):
    return [x * y for x, y in zip(xs, ys)]


def ones(n):
    return [sp.Integer(1) for _ in range(n)]


def eq_vec(xs, ys):
    return all(sp.simplify(x - y) == 0 for x, y in zip(xs, ys))


def check(n=4):
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))
    x = list(sp.symbols(f"x0:{n}", complex=True))
    y = list(sp.symbols(f"y0:{n}", complex=True))
    omega_vec = ones(n)

    # vector state and its finite-sum form
    omega_a = inner(omega_vec, mul(a, omega_vec))
    assert sp.simplify(omega_a - sum(a)) == 0

    # cyclicity
    assert eq_vec(mul(x, omega_vec), x)

    # representation laws
    assert eq_vec(mul(add(a, b), x), add(mul(a, x), mul(b, x)))
    assert eq_vec(mul(mul(a, b), x), mul(a, mul(b, x)))
    assert eq_vec(mul(omega_vec, x), x)

    # involution/product reversal
    assert eq_vec(involution(mul(a, b)), mul(involution(b), involution(a)))

    # adjoint relation
    lhs = inner(mul(a, x), y)
    rhs = inner(x, mul(involution(a), y))
    assert sp.simplify(lhs - rhs) == 0


def main():
    for n in range(1, 6):
        check(n)
    print("finite n-point GNS checks ok")


if __name__ == "__main__":
    main()
