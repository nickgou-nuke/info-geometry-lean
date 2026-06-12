#!/usr/bin/env python3
"""SymPy twin for `BraidParafermionClosure.lean`.

Verified here:
- 2x2 block embedding into 3x3 preserves multiplication;
- explicit braid generators satisfy the Artin relation;
- an exact Z/3Z additive winding closes after three turns.

The script does not prove physical parafermions, SU(3) color confinement,
Lorentz covariance, or LLM thermal dynamics.
"""

from __future__ import annotations

import sympy as sp


def block_embed_2x2(A: sp.Matrix) -> sp.Matrix:
    return sp.Matrix(
        [
            [A[0, 0], A[0, 1], 0],
            [A[1, 0], A[1, 1], 0],
            [0, 0, 1],
        ]
    )


def main() -> None:
    print("--- SymPy Twin: Braid Parafermion Finite Closure ---")

    a, b, c, d, e, f, g, h, t = sp.symbols("a b c d e f g h t")
    A = sp.Matrix([[a, b], [c, d]])
    B = sp.Matrix([[e, f], [g, h]])

    assert sp.simplify(block_embed_2x2(A * B) - block_embed_2x2(A) * block_embed_2x2(B)) == sp.zeros(3)
    print("2x2 -> 3x3 block embedding preserves multiplication: OK")

    sigma_1 = sp.Matrix([[1 - t, t, 0], [1, 0, 0], [0, 0, 1]])
    sigma_2 = sp.Matrix([[1, 0, 0], [0, 1 - t, t], [0, 1, 0]])
    assert sp.simplify(sigma_1 * sigma_2 * sigma_1 - sigma_2 * sigma_1 * sigma_2) == sp.zeros(3)
    print("Artin relation sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2: OK")

    z3_unit = 1
    assert (z3_unit + z3_unit + z3_unit) % 3 == 0
    assert z3_unit % 3 != 0
    print("Z/3Z unit phase closes after three windings and is nonzero: OK")

    print("[SUCCESS] finite braid/phase closure verified.")


if __name__ == "__main__":
    main()
