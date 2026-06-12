#!/usr/bin/env python3
"""Finite witness for MD 013 Clifford algebraic structures.

Mirrors `InfoGeometry.Physics.MD013CliffordAlgebraicStructures`.

Verified theorem-safe content only:
* a nontrivial idempotent gives zero-divisor witnesses e(1-e)=0=(1-e)e;
* a square-zero nonzero nilpotent gives a nontrivial multiplication-kernel witness;
* one-mode CAR matrix units E12/E21 are square-zero and produce projectors.

No Clifford bundle, Chevalley bundle identification, Dirac-operator identity,
spin-structure existence, module classification, primitive/minimal ideal
classification, or index formula is claimed.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_nonzero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced == sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} unexpectedly zero")


def main() -> int:
    print("=" * 72)
    print("MD 013 FINITE CLIFFORD ALGEBRAIC STRUCTURES")
    print("=" * 72)

    I2 = sp.eye(2)
    E11 = sp.Matrix([[1, 0], [0, 0]])
    E22 = sp.Matrix([[0, 0], [0, 1]])
    E12 = sp.Matrix([[0, 1], [0, 0]])
    E21 = sp.Matrix([[0, 0], [1, 0]])

    # Idempotent as zero divisor.
    e = E11
    complement = I2 - e
    assert_matrix_zero(e * e - e, "E11 idempotent")
    assert_matrix_nonzero(e, "E11 nonzero")
    assert_matrix_nonzero(complement, "1-E11 nonzero")
    assert_matrix_zero(e * complement, "idempotent left zero-divisor witness")
    assert_matrix_zero(complement * e, "idempotent right zero-divisor witness")
    print("nontrivial idempotent zero-divisor witnesses: OK")

    # Nilpotents and kernel witnesses.
    assert_matrix_zero(E12 * E12, "E12 square-zero nilpotent")
    assert_matrix_zero(E21 * E21, "E21 square-zero nilpotent")
    assert_matrix_nonzero(E12, "E12 nonzero")
    assert_matrix_nonzero(E21, "E21 nonzero")
    assert_matrix_zero(E12 * E12, "left kernel witness for E12")
    assert_matrix_zero(E21 * E21, "left kernel witness for E21")
    print("square-zero nilpotent zero-divisor witnesses: OK")

    # One-mode CAR and resulting projectors.
    assert_matrix_zero(E12 * E21 - E11, "E12 E21 = E11")
    assert_matrix_zero(E21 * E12 - E22, "E21 E12 = E22")
    assert_matrix_zero(E12 * E21 + E21 * E12 - (E11 + E22), "one-mode CAR anticommutator")
    assert_matrix_zero((E12 * E21) ** 2 - E12 * E21, "CAR left product projector")
    assert_matrix_zero((E21 * E12) ** 2 - E21 * E12, "CAR right product projector")
    assert_matrix_zero(E11 + E22 - I2, "projector partition of identity")
    print("one-mode CAR/projector algebra: OK")

    print("=" * 72)
    print("MD 013 FINITE CLIFFORD ALGEBRAIC STRUCTURES VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
