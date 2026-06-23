#!/usr/bin/env python3
"""Finite-support GNS bounded-operator mirror.

The bounded operator `liftOp(a)` is represented by the diagonal matrix of the
active coordinates of `a`.  Addition, multiplication/composition, and unit laws
mirror the Lean `ContinuousLinearMap` representation laws.
"""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def diag_op(a, mask):
    return sp.diag(*active(a, mask))


def main():
    n = 5
    mask = (True, False, True, True, False)
    m = sum(mask)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    b = list(sp.symbols(f"b0:{n}", complex=True))
    x = sp.Matrix(sp.symbols(f"x0:{m}", complex=True))

    A = diag_op(a, mask)
    B = diag_op(b, mask)
    AB = diag_op([ai * bi for ai, bi in zip(a, b)], mask)
    AplusB = diag_op([ai + bi for ai, bi in zip(a, b)], mask)
    I = diag_op([sp.Integer(1)] * n, mask)

    assert sp.simplify(A * x - sp.Matrix([ai * xi for ai, xi in zip(active(a, mask), x)])) == sp.zeros(m, 1)
    assert sp.simplify(AplusB - (A + B)) == sp.zeros(m, m)
    assert sp.simplify(AB - (A * B)) == sp.zeros(m, m)
    assert sp.simplify(I - sp.eye(m)) == sp.zeros(m, m)

    print("finite-support GNS bounded-operator checks ok")


if __name__ == "__main__":
    main()
