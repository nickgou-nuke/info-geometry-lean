#!/usr/bin/env python3
"""Finite witness for MD 014 Z3 projector and extension algebra.

Mirrors `InfoGeometry.Physics.MD014TriSpinZ3Projectors`.

Verified theorem-safe content only:
* three orthogonal diagonal sector projectors on C^3;
* Z3 phase operator sector readouts and cube identity;
* a finite central-extension product law on a finite base example, with an
  explicitly associative/trivial cocycle table.

No nontrivial Spin(1,3) central extension, Lie-group topology, conformal
embedding, representation classification, three-generation physics, CP
violation, or Yukawa/mixing theorem is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_equal(a, b, label: str) -> None:
    if a != b:
        raise AssertionError(f"{label} failed: {a!r} != {b!r}")


def main() -> int:
    print("=" * 72)
    print("MD 014 FINITE Z3 PROJECTOR / EXTENSION ALGEBRA")
    print("=" * 72)

    I3 = sp.eye(3)
    P0 = sp.diag(1, 0, 0)
    P1 = sp.diag(0, 1, 0)
    P2 = sp.diag(0, 0, 1)
    zero3 = sp.zeros(3)

    for name, P in [("P0", P0), ("P1", P1), ("P2", P2)]:
        assert_matrix_zero(P * P - P, f"{name} idempotent")
    assert_matrix_zero(P0 * P1, "P0 P1 orthogonal")
    assert_matrix_zero(P1 * P2, "P1 P2 orthogonal")
    assert_matrix_zero(P2 * P0, "P2 P0 orthogonal")
    assert_matrix_zero(P0 + P1 + P2 - I3, "projector sum identity")
    print("orthogonal Z3 sector projectors: OK")

    omega = sp.exp(2 * sp.pi * sp.I / 3)
    # Use algebraic root to simplify exactly.
    omega = sp.Rational(-1, 2) + sp.sqrt(3) * sp.I / 2
    Z = P0 + omega * P1 + omega**2 * P2
    assert_matrix_zero(Z * P0 - P0, "sector 0 phase")
    assert_matrix_zero(Z * P1 - omega * P1, "sector 1 phase")
    assert_matrix_zero(Z * P2 - omega**2 * P2, "sector 2 phase")
    assert_matrix_zero(Z**3 - I3, "Z3 phase cube identity")
    print("Z3 phase sector readouts: OK")

    # Finite central extension product over a toy associative base Z2 with
    # trivial Z3-valued cocycle.  This witnesses the product law, not a
    # nontrivial Spin(1,3) extension.
    def base_mul(g: int, h: int) -> int:
        return (g + h) % 2

    def tau(g: int, h: int) -> int:
        return 0

    def ext_mul(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
        g, a = x
        h, b = y
        return (base_mul(g, h), (a + b + tau(g, h)) % 3)

    elements = [(g, a) for g in range(2) for a in range(3)]
    for x in elements:
        for y in elements:
            assert_equal(ext_mul(x, y)[0], base_mul(x[0], y[0]), "projection to base product")
            for z in elements:
                assert_equal(ext_mul(ext_mul(x, y), z), ext_mul(x, ext_mul(y, z)), "extension associativity")
    print("finite central-extension product law: OK")

    print("=" * 72)
    print("MD 014 FINITE Z3 PROJECTOR / EXTENSION ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
