#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.Carrier.Bridge`.

The Lean owner file proves the generic bridge laws from the `TripleAlgebra` and
`SupergradedHopping` interfaces.  This script supplies a concrete finite matrix
model: a projection P, a nilpotent transition N, and a null channel L = N under
a trace-like pairing tr(XY).
"""

from __future__ import annotations

import sympy as sp


def trace_pairing(x: sp.Matrix, y: sp.Matrix) -> sp.Expr:
    """Trace-like bilinear pairing tr(XY)."""
    return sp.trace(x * y)


def main() -> None:
    print("--- SymPy Twin: Carrier Triple Algebra Bridge ---")

    P = sp.Matrix([[1, 0], [0, 0]])
    N = sp.Matrix([[0, 1], [0, 0]])
    L = N

    idempotent_defect = sp.simplify(P * P - P)
    nilpotent_square = sp.simplify(N * N)
    null_square = sp.simplify(L * L)
    null_pairing = sp.simplify(trace_pairing(L, L))

    print(f"P^2 - P = {idempotent_defect}")
    print(f"N^2 = {nilpotent_square}")
    print(f"L^2 = {null_square}")
    print(f"tr(L L) = {null_pairing}")

    assert idempotent_defect == sp.zeros(2)
    assert nilpotent_square == sp.zeros(2)
    assert null_square == sp.zeros(2)
    assert null_pairing == 0

    print("[SUCCESS] finite carrier triple algebra witness matches the Lean bridge laws.")


if __name__ == "__main__":
    main()
