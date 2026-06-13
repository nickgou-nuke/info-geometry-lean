#!/usr/bin/env python3
"""Repaired Section 16: finite Cl+(3,0;C) to M2(C) coordinates.

This mirrors ``lean/InfoGeometry/Section16.lean``.

Closed finite checks:

* the displayed four-coordinate map to 2x2 complex matrices has an explicit
  inverse;
* the three nontrivial basis matrices square to -I;
* their actual cyclic matrix products are verified, repairing the sign mismatch
  in the prose.

Not claimed here:

* a construction of the full complex Clifford algebra;
* Cl(3,0;C) as M2(C) direct-sum M2(C);
* Spin(3;C), SL(2,C), Lorentz double covers, Pauli physics, or Maxwell theory.
"""

from __future__ import annotations

import sympy as sp

I = sp.I


def even_to_matrix(z0, z1, z2, z3):
    return sp.Matrix([
        [z0 - I * z2, I * z1 - z3],
        [I * z1 + z3, z0 + I * z2],
    ])


def matrix_to_even(M):
    return (
        (M[0, 0] + M[1, 1]) / 2,
        -I * (M[0, 1] + M[1, 0]) / 2,
        I * (M[0, 0] - M[1, 1]) / 2,
        (M[1, 0] - M[0, 1]) / 2,
    )


def assert_matrix_zero(M, label: str) -> None:
    reduced = M.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*M.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_tuple_equal(a, b, label: str) -> None:
    for lhs, rhs in zip(a, b):
        if sp.expand(sp.simplify(lhs - rhs)) != 0:
            raise AssertionError(f"{label} failed: {lhs} != {rhs}")


def main() -> None:
    print("=" * 72)
    print("REPAIRED SECTION 16: FINITE BIQUATERNION MATRIX CHECKS")
    print("=" * 72)
    print("Scope: explicit Cl+ coordinate map and basis matrix products.")
    print("Open debt: full Clifford algebra, Spin/SL/Lorentz, and physics claims.")

    z0, z1, z2, z3 = sp.symbols("z0 z1 z2 z3")
    x = (z0, z1, z2, z3)
    assert_tuple_equal(matrix_to_even(even_to_matrix(*x)), x, "matrix_to_even(even_to_matrix(x))")

    a, b, c, d = sp.symbols("a b c d")
    M = sp.Matrix([[a, b], [c, d]])
    assert_matrix_zero(even_to_matrix(*matrix_to_even(M)) - M, "even_to_matrix(matrix_to_even(M))")
    print("  explicit inverse formulas verified")

    ident = sp.eye(2)
    E12 = even_to_matrix(0, 1, 0, 0)
    E23 = even_to_matrix(0, 0, 1, 0)
    E31 = even_to_matrix(0, 0, 0, 1)

    assert_matrix_zero(E12 * E12 + ident, "E12^2 = -I")
    assert_matrix_zero(E23 * E23 + ident, "E23^2 = -I")
    assert_matrix_zero(E31 * E31 + ident, "E31^2 = -I")
    print("  basis squares verified")

    assert_matrix_zero(E12 * E23 - E31, "E12*E23 = E31")
    assert_matrix_zero(E23 * E31 - E12, "E23*E31 = E12")
    assert_matrix_zero(E31 * E12 - E23, "E31*E12 = E23")
    print("  cyclic basis products verified")

    print("=" * 72)
    print("[SUCCESS] Section 16 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
