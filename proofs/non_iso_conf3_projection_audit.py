#!/usr/bin/env python3
"""Projection audit for the non-isotropic Conf_3 quadric cohomology fork.

This script checks the point that matters for theorem honesty:

* the three quadric divisors q12, q13, q23 are independent at a smooth triple
  intersection witness;
* the literal logarithmic Arnold relation for dlog(qij) is not an identity;
* the rank-24 Orlik--Solomon alpha model is therefore a quotient/projection
  branch, not the literal dlog algebra of the quadric divisors;
* the rank-32 product/Leray branch is finite bookkeeping and still requires the
  Dupont/Gysin/de Rham comparison interface to be the actual cohomology theorem.
"""

from __future__ import annotations

from itertools import combinations

import sympy as sp


SIG = (1, -1, -1, -1)


def q_mink(v):
    return sum(s * x * x for s, x in zip(SIG, v))


def dlog_gradient(poly, coords):
    return [sp.diff(poly, c) / poly for c in coords]


def wedge_coeff(u, v, i, j):
    return sp.simplify(u[i] * v[j] - u[j] * v[i])


def common_denominator_arnold_coeff(g12, g23, g13, q12, q23, q13, i, j):
    """Coefficient of

      dlog(q12)^dlog(q23) - dlog(q12)^dlog(q13)
        + dlog(q23)^dlog(q13)

    after multiplying by q12*q23*q13.
    """
    return sp.simplify(
        wedge_coeff([sp.diff(q12, c) for c in COORDS], [sp.diff(q23, c) for c in COORDS], i, j) * q13
        - wedge_coeff([sp.diff(q12, c) for c in COORDS], [sp.diff(q13, c) for c in COORDS], i, j) * q23
        + wedge_coeff([sp.diff(q23, c) for c in COORDS], [sp.diff(q13, c) for c in COORDS], i, j) * q12
    )


x = sp.symbols("x0:4")
y = sp.symbols("y0:4")
z = sp.symbols("z0:4")
COORDS = (*x, *y, *z)


def main() -> None:
    q12 = q_mink([x[i] - y[i] for i in range(4)])
    q23 = q_mink([y[i] - z[i] for i in range(4)])
    q13 = q_mink([x[i] - z[i] for i in range(4)])

    # Non-isotropic sample used to test literal dlog Arnold failure.
    sample = {
        x[0]: 1, x[1]: 0, x[2]: 0, x[3]: 0,
        y[0]: 0, y[1]: 2, y[2]: 0, y[3]: 0,
        z[0]: 0, z[1]: 0, z[2]: 3, z[3]: 0,
    }
    qvals = tuple(sp.simplify(p.subs(sample)) for p in (q12, q23, q13))
    assert qvals == (-3, -13, -8)

    g12 = dlog_gradient(q12, COORDS)
    g23 = dlog_gradient(q23, COORDS)
    g13 = dlog_gradient(q13, COORDS)
    coeffs = {
        (i, j): sp.simplify(
            common_denominator_arnold_coeff(g12, g23, g13, q12, q23, q13, i, j).subs(sample)
        )
        for i, j in combinations(range(len(COORDS)), 2)
    }
    nonzero = {ij: c for ij, c in coeffs.items() if c != 0}
    assert coeffs[(0, 4)] == 52
    assert nonzero

    # Smooth triple-intersection independence witness over C for the three
    # equations q(a)=q(b)=q(a-b)=0 after translation.  A polynomial dependence
    # among the three quadrics would force Jacobian rank < 3 generically.
    I = sp.I
    a = sp.symbols("a0:4")
    b = sp.symbols("b0:4")
    qa = sum(ai * ai for ai in a)
    qb = sum(bi * bi for bi in b)
    qab = sum((a[i] - b[i]) ** 2 for i in range(4))
    witness = {
        a[0]: 1, a[1]: I, a[2]: 0, a[3]: 0,
        b[0]: 0, b[1]: 0, b[2]: 1, b[3]: I,
    }
    values = [sp.simplify(p.subs(witness)) for p in (qa, qb, qab)]
    jac = sp.Matrix([[sp.diff(p, v) for v in (*a, *b)] for p in (qa, qb, qab)])
    rank = jac.subs(witness).rank()
    assert values == [0, 0, 0]
    assert rank == 3

    t = sp.symbols("t")
    product_leray = sp.expand((1 + t) ** 3 * (1 + t ** 3) ** 2)
    os_alpha_projection = sp.expand((1 + 3 * t + 2 * t**2) * (1 + t ** 3) ** 2)
    assert product_leray.subs(t, 1) == 32
    assert os_alpha_projection.subs(t, 1) == 24

    print("=== non_iso_conf3_projection_audit.py ===")
    print("non-isotropic sample q12,q23,q13 =", qvals)
    print("literal dlog Arnold obstruction coefficient dx0^dy0 =", coeffs[(0, 4)])
    print("nonzero Arnold-obstruction 2-form coefficients =", len(nonzero), "of", len(coeffs))
    print("triple-intersection q values =", values, "Jacobian rank =", rank)
    print("D=4 product/Leray branch:", product_leray, "rank", product_leray.subs(t, 1))
    print("D=4 OS-alpha projection:", os_alpha_projection, "rank", os_alpha_projection.subs(t, 1))
    print("verdict: OS-alpha is a quotient/projection branch, not a literal quadric dlog identity.")


if __name__ == "__main__":
    main()
