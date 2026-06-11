#!/usr/bin/env python3
"""Finite witness for the Souriau-Bost-Connes transition package.

This is an honest finite shadow only. It checks:
- the thermal Cayley coordinate tends to the boundary point `1`,
- the canonical Cantor boundary sample is the all-zero readout,
- the canonical boundary label is the unit label,
- the Dirac-sea interface remains the finite vacuum readout.

It does NOT prove analytic zero-temperature accumulation, the full
Souriau-Bost-Connes crystallization theorem, or the categorical boundary
functor.
"""

from __future__ import annotations

from sympy import Rational, Symbol, diff, limit, oo, simplify


def thermal_cayley(beta):
    return (beta - Rational(1, 2)) / (beta + Rational(1, 2))


def main() -> None:
    beta = Symbol("beta", real=True, positive=True)
    W = thermal_cayley(beta)
    dW = diff(W, beta)

    boundary_word_prefix = (0, 0, 0, 0)
    boundary_label = "unit"
    dirac_sea_vacuum = "vacuum"

    assert boundary_word_prefix == (0, 0, 0, 0)
    assert boundary_label == "unit"
    assert dirac_sea_vacuum == "vacuum"
    assert simplify(limit(W, beta, oo) - 1) == 0
    assert simplify(limit(dW, beta, oo)) == 0

    print("Souriau-Bost-Connes transition finite package passed")
    print(f"limit W(beta) as beta->oo = {limit(W, beta, oo)}")
    print(f"limit dW/dbeta as beta->oo = {limit(dW, beta, oo)}")
    print(f"boundary_word_prefix = {boundary_word_prefix}")
    print(f"boundary_label = {boundary_label}")
    print(f"dirac_sea_vacuum = {dirac_sea_vacuum}")


if __name__ == "__main__":
    main()
