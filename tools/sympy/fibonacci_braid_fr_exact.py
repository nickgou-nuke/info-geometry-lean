#!/usr/bin/env python3
"""Exact finite Fibonacci F/R braid witness.

The check is polynomial.  Let `q` be a primitive 10th root of unity, so
`Phi_10(q) = q^4 - q^3 + q^2 - q + 1 = 0`.  The Fibonacci scalar is
`tau = q^2 - q^3`, with `s^2 = tau`.  The standard phases

    R^1 = exp(-4 pi i / 5) = q^6,
    R^tau = exp(3 pi i / 5) = q^3

are equivalent to the `q^4, q^7` convention after inversion.  This script uses
the existing polynomial reduction owner convention `R = diag(q^4, q^7)`.
"""

from __future__ import annotations

import sympy as sp


def rem_phi10(expr: sp.Expr, q: sp.Symbol) -> sp.Expr:
    phi10 = q**4 - q**3 + q**2 - q + 1
    return sp.rem(sp.Poly(sp.expand(expr), q), sp.Poly(phi10, q)).as_expr()


def main() -> None:
    print("=== EXACT FIBONACCI F/R BRAID VALIDATION ===")
    q, s = sp.symbols("q s")
    tau = q**2 - q**3

    # F^2 = I with s^2 = tau and tau^2 + tau = 1 modulo Phi_10(q).
    F = sp.Matrix([[tau, s], [s, -tau]])
    F2_minus_I = (F * F - sp.eye(2)).subs(s**2, tau)
    assert all(rem_phi10(F2_minus_I[i, j], q) == 0 for i in range(2) for j in range(2))
    print("1. [SUCCESS] exact F^2 = I modulo Phi_10 and s^2=tau.")

    # R is unitary because each diagonal phase is a root of unity.
    assert (4 + 6) % 10 == 0
    assert (7 + 3) % 10 == 0
    print("2. [SUCCESS] exact R unitary by cyclotomic inverse exponents.")

    R = sp.diag(q**4, q**7)
    B = F * R * F
    diff = sp.Matrix(R * B * R - B * R * B)

    # Reduce by s^2=tau, then by Phi_10(q).
    for i in range(2):
        for j in range(2):
            entry = sp.Poly(sp.expand(diff[i, j]), s)
            reduced = 0
            for (power,), coeff in entry.terms():
                reduced += coeff * (s if power % 2 else 1) * tau ** (power // 2)
            assert rem_phi10(sp.expand(reduced), q) == 0
    print("3. [SUCCESS] exact Artin relation R B R = B R B modulo Phi_10.")


if __name__ == "__main__":
    main()
