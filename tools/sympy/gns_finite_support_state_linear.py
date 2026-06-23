#!/usr/bin/env python3
"""Finite-support GNS state linearity/star compatibility mirror."""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def omega(xs, mask):
    return sum(active(xs, mask))


def main():
    n = 5
    mask = (True, False, True, True, False)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))
    c = sp.symbols("c", complex=True)

    add = [ai + bi for ai, bi in zip(a, b)]
    neg = [-ai for ai in a]
    sub = [ai - bi for ai, bi in zip(a, b)]
    smul = [c * ai for ai in a]
    invol = [sp.conjugate(ai) for ai in a]

    assert sp.simplify(omega(add, mask) - (omega(a, mask) + omega(b, mask))) == 0
    assert sp.simplify(omega(neg, mask) + omega(a, mask)) == 0
    assert sp.simplify(omega(sub, mask) - (omega(a, mask) - omega(b, mask))) == 0
    assert sp.simplify(omega(smul, mask) - c * omega(a, mask)) == 0
    assert sp.simplify(omega(invol, mask) - sp.conjugate(omega(a, mask))) == 0

    print("finite-support GNS state linearity checks ok")


if __name__ == "__main__":
    main()
