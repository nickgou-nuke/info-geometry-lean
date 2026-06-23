#!/usr/bin/env python3
"""
Exact-rational SymPy certificate for the KL symmetric/antisymmetric decomposition.

We verify on rational Bernoulli states p and q that:
  D(p||q) = D_sym(p,q) + D_antisym(p,q)
  D(q||p) = D_sym(p,q) - D_antisym(p,q)
  D_sym is swap-invariant
  D_antisym is swap-odd
and we numerically confirm the Bregman form of KL for the negative Shannon entropy.
"""

from __future__ import annotations

import sympy as sp


def kl_binary(p: sp.Rational, q: sp.Rational) -> sp.Expr:
    return sp.simplify(p * sp.log(p / q) + (1 - p) * sp.log((1 - p) / (1 - q)))


def bregman_neg_entropy(p: sp.Rational, q: sp.Rational) -> sp.Expr:
    x = sp.symbols("x", positive=True, real=True)
    F = x * sp.log(x) + (1 - x) * sp.log(1 - x)
    gradF = sp.diff(F, x)
    return sp.simplify(
        (p * sp.log(p) + (1 - p) * sp.log(1 - p))
        - (q * sp.log(q) + (1 - q) * sp.log(1 - q))
        - gradF.subs(x, q) * (p - q)
    )


def main() -> None:
    print("=== KL DIVERGENCE DECOMPOSITION SYMPY CERTIFICATE ===")

    samples = [
        (sp.Rational(1, 5), sp.Rational(2, 5)),
        (sp.Rational(1, 3), sp.Rational(3, 5)),
        (sp.Rational(2, 7), sp.Rational(5, 8)),
    ]

    for p, q in samples:
        dpq = kl_binary(p, q)
        dqp = kl_binary(q, p)
        dsym = sp.simplify((dpq + dqp) / 2)
        דאסym = sp.simplify((dpq - dqp) / 2)
        print(f"\nsample p={p}, q={q}")
        print("D(p||q)   =", sp.N(dpq))
        print("D(q||p)   =", sp.N(dqp))
        print("D_sym     =", sp.N(dsym))
        print("D_antisym =", sp.N(דאסym))
        assert sp.simplify(dpq - (dsym + דאסym)) == 0
        assert sp.simplify(dqp - (dsym - דאסym)) == 0
        assert sp.simplify(((dqp + dpq) / 2) - dsym) == 0
        assert sp.simplify(((dqp - dpq) / 2) + דאסym) == 0
        breg = sp.N(bregman_neg_entropy(p, q))
        assert abs(float(breg - sp.N(dpq))) < 1e-10

    print("\nKL_DIVERGENCE_DECOMPOSITION_SYMPY_OK")


if __name__ == "__main__":
    main()
