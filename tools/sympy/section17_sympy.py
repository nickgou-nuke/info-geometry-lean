#!/usr/bin/env python3
"""Repaired Section 17: finite biquaternion matrix checks.

This mirrors ``lean/InfoGeometry/Section17.lean``.

Closed finite checks:

* the displayed biquaternion coordinate map to M2(C) has an explicit inverse;
* the basis matrices for i, j, k satisfy Hamilton's multiplication table;
* the Section 17 map is the Section 16 even-coordinate map after a permutation
  of imaginary coordinates.

Not claimed here:

* tensor-product construction of H tensor C over R;
* full complex Clifford algebra or direct-sum theorem;
* Spin/SL/Lorentz, Pauli physics, or Maxwell theory.
"""

from __future__ import annotations

import sympy as sp

I = sp.I


def biquat_to_matrix(c0, c1, c2, c3):
    return sp.Matrix([
        [c0 + I * c1, c2 + I * c3],
        [-c2 + I * c3, c0 - I * c1],
    ])


def matrix_to_biquat(M):
    return (
        (M[0, 0] + M[1, 1]) / 2,
        -I * (M[0, 0] - M[1, 1]) / 2,
        (M[0, 1] - M[1, 0]) / 2,
        -I * (M[0, 1] + M[1, 0]) / 2,
    )


def section16_even_to_matrix(z0, z1, z2, z3):
    return sp.Matrix([
        [z0 - I * z2, I * z1 - z3],
        [I * z1 + z3, z0 + I * z2],
    ])


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
    print("REPAIRED SECTION 17: FINITE BIQUATERNION MATRIX CHECKS")
    print("=" * 72)
    print("Scope: explicit H_C coordinate map and Hamilton basis products.")
    print("Open debt: full Clifford/tensor algebra, Spin/SL/Lorentz, and physics claims.")

    c0, c1, c2, c3 = sp.symbols("c0 c1 c2 c3")
    q = (c0, c1, c2, c3)
    assert_tuple_equal(matrix_to_biquat(biquat_to_matrix(*q)), q, "matrix_to_biquat(biquat_to_matrix(q))")

    a, b, c, d = sp.symbols("a b c d")
    M = sp.Matrix([[a, b], [c, d]])
    assert_matrix_zero(biquat_to_matrix(*matrix_to_biquat(M)) - M, "biquat_to_matrix(matrix_to_biquat(M))")
    print("  explicit inverse formulas verified")

    ident = sp.eye(2)
    Qi = biquat_to_matrix(0, 1, 0, 0)
    Qj = biquat_to_matrix(0, 0, 1, 0)
    Qk = biquat_to_matrix(0, 0, 0, 1)

    assert_matrix_zero(Qi * Qi + ident, "i^2 = -1")
    assert_matrix_zero(Qj * Qj + ident, "j^2 = -1")
    assert_matrix_zero(Qk * Qk + ident, "k^2 = -1")
    assert_matrix_zero(Qi * Qj - Qk, "ij = k")
    assert_matrix_zero(Qj * Qk - Qi, "jk = i")
    assert_matrix_zero(Qk * Qi - Qj, "ki = j")
    assert_matrix_zero(Qj * Qi + Qk, "ji = -k")
    assert_matrix_zero(Qk * Qj + Qi, "kj = -i")
    assert_matrix_zero(Qi * Qk + Qj, "ik = -j")
    print("  Hamilton basis products verified")

    assert_matrix_zero(
        biquat_to_matrix(*q) - section16_even_to_matrix(c0, c3, -c1, -c2),
        "Section 17 map as permuted Section 16 map",
    )
    print("  Section 16 coordinate permutation bridge verified")

    print("=" * 72)
    print("[SUCCESS] Section 17 theorem-safe finite checks verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
