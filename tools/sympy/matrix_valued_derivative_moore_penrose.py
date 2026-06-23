#!/usr/bin/env python3
"""
Exact-rational SymPy witness for the Moore-Penrose matrix-valued derivative lane.

The finite certificate checks three algebraic facts that mirror the Lean owner
module:

1. A singular projector is its own Moore-Penrose inverse.
2. Constant matrix-valued functions have zero generalized difference quotient.
3. Left multiplication commutes with the generalized difference quotient.
"""

from __future__ import annotations

import sympy as sp


def generalized_difference_quotient(f, X, H, Hplus):
    return (f(X + H) - f(X)) * Hplus


def main() -> None:
    print("=== SYMPY: MATRIX-VALUED DERIVATIVE / MOORE-PENROSE WITNESS ===")

    H = sp.Matrix([[sp.Rational(1), 0], [0, 0]])
    Hplus = sp.Matrix([[sp.Rational(1), 0], [0, 0]])
    A = sp.Matrix([[sp.Rational(2), sp.Rational(1)], [0, sp.Rational(3)]])
    X0 = sp.zeros(2)
    C = sp.Matrix([[sp.Rational(7), sp.Rational(3)], [sp.Rational(5), sp.Rational(11)]])

    print("\n1. Singular projector H:")
    sp.pprint(H)
    print("H * H * H:")
    sp.pprint(H * H * H)
    print("Hplus:")
    sp.pprint(Hplus)
    assert H * Hplus * H == H
    assert Hplus * H * Hplus == Hplus
    assert (H * Hplus).T == H * Hplus
    assert (Hplus * H).T == Hplus * H

    const_dq = generalized_difference_quotient(lambda _: C, X0, H, Hplus)
    print("\n2. Constant generalized difference quotient:")
    sp.pprint(const_dq)
    assert const_dq == sp.zeros(2)

    square = lambda M: M * M
    dq_square = generalized_difference_quotient(square, X0, H, Hplus)
    print("\n3. Square-map generalized difference quotient at X0 = 0:")
    sp.pprint(dq_square)

    dq_left = generalized_difference_quotient(lambda M: A * square(M), X0, H, Hplus)
    rhs_left = A * dq_square
    print("\n4. Left-multiplication compatibility residual:")
    sp.pprint(sp.simplify(dq_left - rhs_left))
    assert dq_left == rhs_left

    print("\nCONCLUSION:")
    print("  - The singular projector is Moore-Penrose self-inverse.")
    print("  - Constant matrix-valued quotients vanish.")
    print("  - Left multiplication commutes with the generalized difference quotient.")


if __name__ == "__main__":
    main()
