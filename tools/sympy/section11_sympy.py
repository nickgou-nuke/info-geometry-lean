#!/usr/bin/env python3
"""Section 11: finite algebraic Bianchi identities.

Exact SymPy companion to ``lean/InfoGeometry/Section11.lean``.

It verifies:

* a zero cyclic vector/Riemann Bianchi sum is preserved by a linear spinorial
  readout;
* the contracted Bianchi identity is the algebraic cancellation
  ``divRicci - 1/2 gradScalar = 0`` once ``divRicci = 1/2 gradScalar``.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    diff = matrix.applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


def cyclic_sum(x: sp.Matrix, y: sp.Matrix, z: sp.Matrix) -> sp.Matrix:
    return x + y + z


def main() -> int:
    print("=" * 72)
    print("SECTION 11: BIANCHI IDENTITIES -- FINITE ALGEBRAIC CHECK")
    print("=" * 72)

    print("\n11.1 First Bianchi under linear spinorial readout")
    r0 = sp.Matrix(sp.symbols("r0:16")).reshape(16, 1)
    r1 = sp.Matrix(sp.symbols("s0:16")).reshape(16, 1)
    r2 = -r0 - r1
    readout = sp.Matrix(4, 16, sp.symbols("L0:64"))
    spin0 = readout * r0
    spin1 = readout * r1
    spin2 = readout * r2
    assert_matrix_zero("L(R0) + L(R1) + L(R2) = 0 when R0+R1+R2=0",
                       cyclic_sum(spin0, spin1, spin2))

    print("\n11.2 Contracted Bianchi identity")
    grad = sp.Matrix(sp.symbols("g0:4"))
    div_ricci = sp.Rational(1, 2) * grad
    einstein_divergence = div_ricci - sp.Rational(1, 2) * grad
    assert_matrix_zero("div Einstein = div Ricci - 1/2 grad scalar = 0", einstein_divergence)

    print("\nSECTION 11 VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

