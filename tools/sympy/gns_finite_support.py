#!/usr/bin/env python3
"""Finite-support GNS quotient mirror.

Ambient algebra: C^n.  A boolean support mask selects the coordinates seen by
the state.  The concrete GNS space is C^support, i.e. restriction to active
coordinates.  Elements differing off support have the same GNS vector.
"""

import sympy as sp


def restrict(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def inner(xs, ys):
    return sum(sp.conjugate(x) * y for x, y in zip(xs, ys))


def involution(xs):
    return [sp.conjugate(x) for x in xs]


def add(xs, ys):
    return [x + y for x, y in zip(xs, ys)]


def sub(xs, ys):
    return [x - y for x, y in zip(xs, ys)]


def mul(xs, ys):
    return [x * y for x, y in zip(xs, ys)]


def lift_mul(a, x_support, mask):
    out = []
    k = 0
    for ai, m in zip(a, mask):
        if m:
            out.append(ai * x_support[k])
            k += 1
    return out


def eq_vec(xs, ys):
    return all(sp.simplify(x - y) == 0 for x, y in zip(xs, ys))


def check(n=5, mask=(True, False, True, False, True)):
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))
    x = list(sp.symbols(f"x0:{sum(mask)}", complex=True))
    y = list(sp.symbols(f"y0:{sum(mask)}", complex=True))
    omega_vec = [sp.Integer(1)] * sum(mask)

    # vector state: <Ω, restrict(a)> = sum over support
    lhs = inner(omega_vec, restrict(a, mask))
    rhs = sum(restrict(a, mask))
    assert sp.simplify(lhs - rhs) == 0

    # quotient equality iff active difference vanishes
    diff_active = restrict(sub(a, b), mask)
    same_active = [ra - rb for ra, rb in zip(restrict(a, mask), restrict(b, mask))]
    assert eq_vec(diff_active, same_active)

    # cyclic witness: every support vector is restriction of an ambient vector
    ambient_x = []
    it = iter(x)
    for m in mask:
        ambient_x.append(next(it) if m else sp.Integer(0))
    assert eq_vec(restrict(ambient_x, mask), x)

    # representation laws on support
    assert eq_vec(lift_mul(add(a, b), x, mask), add(lift_mul(a, x, mask), lift_mul(b, x, mask)))
    assert eq_vec(lift_mul(mul(a, b), x, mask), lift_mul(a, lift_mul(b, x, mask), mask))
    assert eq_vec(lift_mul([sp.Integer(1)] * n, x, mask), x)

    # adjoint relation on support
    lhs_adj = inner(lift_mul(a, x, mask), y)
    rhs_adj = inner(x, lift_mul(involution(a), y, mask))
    assert sp.simplify(lhs_adj - rhs_adj) == 0


def main():
    check()
    check(4, (False, True, True, False))
    check(3, (True, True, True))
    print("finite-support GNS quotient checks ok")


if __name__ == "__main__":
    main()
