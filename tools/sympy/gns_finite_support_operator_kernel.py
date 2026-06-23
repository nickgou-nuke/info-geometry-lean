#!/usr/bin/env python3
"""Finite-support GNS representation kernel mirror.

The diagonal representation only sees active coordinates.  Hence two algebra
elements have the same represented operator iff their active restrictions are
equal; the zero represented operator iff all active coordinates vanish.
"""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def diag_op(a, mask):
    return sp.diag(*active(a, mask))


def main():
    n = 5
    mask = (True, False, True, False, True)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))

    A = diag_op(a, mask)
    B = diag_op(b, mask)
    diff_diag = A - B
    diff_active = [ai - bi for ai, bi in zip(active(a, mask), active(b, mask))]

    # Operator equality is exactly active coordinate equality.
    assert list(diff_diag.diagonal()) == diff_active

    # Zero operator is exactly active nullity.
    Z = diag_op([0] * n, mask)
    assert list((A - Z).diagonal()) == active(a, mask)

    # Full support: diagonal equality determines all coordinates.
    full = (True,) * n
    Af = diag_op(a, full)
    Bf = diag_op(b, full)
    assert list((Af - Bf).diagonal()) == [ai - bi for ai, bi in zip(a, b)]

    print("finite-support GNS operator kernel checks ok")


if __name__ == "__main__":
    main()
