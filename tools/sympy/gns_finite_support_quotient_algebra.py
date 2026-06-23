#!/usr/bin/env python3
"""Finite-support GNS quotient algebra congruence mirror."""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def same(xs, ys, mask):
    return all(sp.simplify(x - y) == 0 for x, y in zip(active(xs, mask), active(ys, mask)))


def add(xs, ys): return [x + y for x, y in zip(xs, ys)]
def neg(xs): return [-x for x in xs]
def smul(c, xs): return [c * x for x in xs]
def mul(xs, ys): return [x * y for x, y in zip(xs, ys)]
def invol(xs): return [sp.conjugate(x) for x in xs]


def main():
    n = 5
    mask = (True, False, True, True, False)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))
    c = sp.symbols("c", complex=True)

    # construct equivalent representatives differing only off support
    a2 = a.copy(); b2 = b.copy()
    for k, m in enumerate(mask):
        if not m:
            a2[k] = sp.symbols(f"u{k}", complex=True)
            b2[k] = sp.symbols(f"v{k}", complex=True)

    assert same(a, a2, mask)
    assert same(b, b2, mask)
    assert same(add(a, b), add(a2, b2), mask)
    assert same(neg(a), neg(a2), mask)
    assert same(smul(c, a), smul(c, a2), mask)
    assert same(mul(a, b), mul(a2, b2), mask)
    assert same(invol(a), invol(a2), mask)
    print("finite-support GNS quotient algebra checks ok")


if __name__ == "__main__":
    main()
