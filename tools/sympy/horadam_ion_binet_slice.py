#!/usr/bin/env python3
"""Finite witness for the Horadam 2^k-ion Binet slice.

Source: preprints201906.0303.v1, "Horadam 2^k-ions", Theorem 1.

This checks the theorem-safe conditional algebra:
  * if alpha^2 = p alpha + q and beta^2 = p beta + q, then
    C_n = A alpha^n - B beta^n satisfies C_{n+2}=p C_{n+1}+q C_n;
  * the coordinate/2^k-ion lift satisfies the same recurrence;
  * with A=b-a beta and B=b-a alpha, the normalized expression
    (A alpha^n - B beta^n)/(alpha-beta) has initial values a,b.

No Cayley-Dickson multiplication, noncommutative Catalan/Cassini identity, or
analytic convergence theorem is asserted.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    a, b, p, q = sp.symbols("a b p q")
    alpha, beta, A, B = sp.symbols("alpha beta A B")
    n = sp.symbols("n", integer=True, nonnegative=True)

    # Check recurrence symbolically by reducing alpha^2 and beta^2.
    def reduce_quad(expr: sp.Expr) -> sp.Expr:
        return sp.expand(expr).xreplace({})

    # Direct algebra for generic n: factor alpha^n and beta^n.
    lhs = A * alpha ** (n + 2) - B * beta ** (n + 2)
    rhs = p * (A * alpha ** (n + 1) - B * beta ** (n + 1)) + q * (A * alpha**n - B * beta**n)
    diff = sp.factor(lhs - rhs)
    expected = sp.factor(A * alpha**n * (alpha**2 - p * alpha - q) - B * beta**n * (beta**2 - p * beta - q))
    assert sp.factor(diff - expected) == 0

    # Numeric algebraic-root sample.
    p0, q0 = 1, 1
    alpha0 = (1 + sp.sqrt(5)) / 2
    beta0 = (1 - sp.sqrt(5)) / 2
    assert sp.simplify(alpha0**2 - p0 * alpha0 - q0) == 0
    assert sp.simplify(beta0**2 - p0 * beta0 - q0) == 0
    A0, B0 = sp.Integer(3), sp.Integer(-2)
    for k in range(8):
        C = lambda m: sp.simplify(A0 * alpha0**m - B0 * beta0**m)
        assert sp.simplify(C(k + 2) - p0 * C(k + 1) - q0 * C(k)) == 0

    # Paper's normalized initial-value constants.
    Ap = b - a * beta
    Bp = b - a * alpha
    W = lambda m: sp.simplify((Ap * alpha**m - Bp * beta**m) / (alpha - beta))
    assert sp.simplify(W(0) - a) == 0
    assert sp.simplify(W(1) - b) == 0

    # Coordinate lift sample, N=8.
    N = 8
    for k in range(5):
        ion_next2 = sp.Matrix([C(k + 2 + s) for s in range(N)])
        ion_rhs = p0 * sp.Matrix([C(k + 1 + s) for s in range(N)]) + q0 * sp.Matrix([C(k + s) for s in range(N)])
        assert sp.simplify(ion_next2 - ion_rhs) == sp.zeros(N, 1)

    print("HORADAM_ION_BINET_SLICE_FINITE_OK")
    print("scope: conditional Binet recurrence and coordinate lift only; no full Cayley-Dickson or infinite-series theorem")


if __name__ == "__main__":
    main()
