#!/usr/bin/env python3
"""Finite-support GNS boundedness mirror.

Checks the finite inequality
  ||a*x||^2 <= K ||x||^2
symbolically at the level of the exact summand identity and numerically for
sample values satisfying K >= max_i |a_i|^2 on the active support.
"""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def lift_mul(a, x, mask):
    out = []
    k = 0
    for ai, m in zip(a, mask):
        if m:
            out.append(ai * x[k])
            k += 1
    return out


def norm_sq_vec(xs):
    return sum(sp.conjugate(x) * x for x in xs)


def main():
    n = 4
    mask = (True, False, True, True)
    a = list(sp.symbols("a0:4", complex=True))
    x = list(sp.symbols("x0:3", complex=True))

    ax = lift_mul(a, x, mask)
    active_a = active(a, mask)

    # Exact summand factorization: |a_i x_i|^2 = |a_i|^2 |x_i|^2.
    for ai, xi, axi in zip(active_a, x, ax):
        lhs = sp.conjugate(axi) * axi
        rhs = (sp.conjugate(ai) * ai) * (sp.conjugate(xi) * xi)
        assert sp.simplify(lhs - rhs) == 0

    # Numeric boundedness samples.
    samples = [
        ([1 + 2j, 9j, -1j, 0.5], [2 - 1j, 3j, -4], 5.0),
        ([0.25, 7, 0.5j, -0.5], [1, -2j, 3 + 4j], 0.25),
    ]
    for avec, xvec, K in samples:
        axv = lift_mul([complex(z) for z in avec], [complex(z) for z in xvec], mask)
        lhs = sum(abs(z) ** 2 for z in axv)
        rhs = K * sum(abs(z) ** 2 for z in xvec)
        assert lhs <= rhs + 1e-9

    print("finite-support GNS boundedness checks ok")


if __name__ == "__main__":
    main()
