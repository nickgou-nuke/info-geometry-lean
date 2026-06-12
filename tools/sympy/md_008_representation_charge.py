#!/usr/bin/env python3
"""Finite witness for MD 008 representation charge lattice.

Mirrors `InfoGeometry.Physics.MD008RepresentationCharge`.

Verified theorem-safe content only:
* A1 + A1 formal roots (±2,0), (0,±2);
* root-lattice shifts are even shifts in both coordinates;
* quotient by root shifts is parity Z2 x Z2 with four representatives;
* matrix units have the already-known left/right σ3 weights.

No full Lie algebra isomorphism, Weyl representation classification,
Lorentz spinoriality theorem, boson/fermion classification, or Standard Model
charge claim is made.
"""

from __future__ import annotations

import itertools
import sympy as sp


def charge(w: tuple[int | sp.Expr, int | sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (sp.Mod(w[0], 2), sp.Mod(w[1], 2))


def add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def root_shift(a, b):
    return (2 * a, 2 * b)


def assert_equal(lhs, rhs, label: str) -> None:
    if lhs != rhs:
        raise AssertionError(f"{label} failed: {lhs} != {rhs}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    print("=" * 72)
    print("MD 008 FINITE REPRESENTATION CHARGE LATTICE")
    print("=" * 72)

    roots = [(2, 0), (-2, 0), (0, 2), (0, -2)]
    for r in roots:
        assert_equal(charge(r), (0, 0), f"root {r} has zero charge")
    print("A1+A1 roots have zero parity charge: OK")

    # Exhaust a representative finite window for root-shift invariance.
    for m, n, a, b in itertools.product(range(-3, 4), repeat=4):
        w = (m, n)
        shifted = add(w, root_shift(a, b))
        assert_equal(charge(shifted), charge(w), f"charge invariant {w},{a},{b}")
    print("root-lattice shift invariance: OK")

    reps = {(0, 0), (1, 0), (0, 1), (1, 1)}
    seen = {charge((m, n)) for m in range(-4, 5) for n in range(-4, 5)}
    assert_equal(seen, reps, "four parity representatives")
    print("four Z2 x Z2 representatives: OK")

    I2 = sp.eye(2)
    s3 = sp.Matrix([[1, 0], [0, -1]])
    E11 = sp.Matrix([[1, 0], [0, 0]])
    E12 = sp.Matrix([[0, 1], [0, 0]])
    E21 = sp.Matrix([[0, 0], [1, 0]])
    E22 = sp.Matrix([[0, 0], [0, 1]])
    data = [
        (E11, (1, 1), "E11"),
        (E12, (1, -1), "E12"),
        (E21, (-1, 1), "E21"),
        (E22, (-1, -1), "E22"),
    ]
    for E, (l, r), name in data:
        assert_matrix_zero(s3 * E - l * E, f"{name} left Cartan weight")
        assert_matrix_zero(E * s3 - r * E, f"{name} right Cartan weight")
        assert_equal(charge((l, r)), (1, 1), f"{name} odd/odd charge")
    print("matrix-unit Cartan weights and charges: OK")

    print("=" * 72)
    print("MD 008 FINITE REPRESENTATION CHARGE LATTICE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
