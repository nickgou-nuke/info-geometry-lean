#!/usr/bin/env python3
"""Sage exact finite Fibonacci F/R braid witness.

Runs with ordinary Python from the Sage environment:

    /home/goutev/miniforge3/envs/sage/bin/python tools/sage/fibonacci_braid_fr_exact.sage.py

The witness is algebraic: work in `QQ[q, s] / (Phi_10(q), s^2 - tau)` with
`tau = q^2 - q^3`.
"""

from __future__ import annotations

from sage.all import Matrix, PolynomialRing, QQ, identity_matrix


def main() -> None:
    print("=== SAGE EXACT FIBONACCI F/R BRAID VALIDATION ===")

    P = PolynomialRing(QQ, names=("q", "s"))
    q, s = P.gens()
    phi10 = q**4 - q**3 + q**2 - q + 1
    tau = q**2 - q**3
    relation_s = s**2 - tau
    quotient = P.quotient([phi10, relation_s], names=("qbar", "sbar"))
    qbar, sbar = quotient.gens()
    taubar = qbar**2 - qbar**3

    F = Matrix(quotient, [[taubar, sbar], [sbar, -taubar]])
    I2 = identity_matrix(quotient, 2)
    assert F * F == I2
    print("1. [SUCCESS] exact F^2 = I in QQ[q,s]/(Phi_10, s^2-tau).")

    # Convention used by the existing finite polynomial owner.
    R = Matrix(quotient, [[qbar**4, 0], [0, qbar**7]])
    R_inv = Matrix(quotient, [[qbar**6, 0], [0, qbar**3]])
    assert R * R_inv == I2
    print("2. [SUCCESS] exact R unitary/invertible via cyclotomic inverse phases.")

    B = F * R * F
    assert R * B * R == B * R * B
    print("3. [SUCCESS] exact Artin relation R B R = B R B.")


if __name__ == "__main__":
    main()
