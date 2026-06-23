#!/usr/bin/env python3
"""Exact-rational SymPy audit for Holographic Souriau Reconstruction.

Finite theorem-honest lane for
`lean/InfoGeometry/Canonical/HolographicSouriauReconstruction.lean`.

It verifies:
* the split `O(5,5)` rational metric is symmetric and involutive;
* the Brillouin twist/glide pair satisfies `T^2 = -I`, `K^2 = I`, `KT = -TK`;
* the rational Chevalley `sl3` color shadow is traceless and commutes with a
  scalar modular laser, so the internal color fiber is not geometrically
  projected by that laser.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(sp.simplify)
    if reduced != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def mat_comm(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def o55_audit() -> None:
    eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    assert eta.T == eta
    assert eta * eta == sp.eye(10)
    assert eta.det() == -1
    print("PASS: O(5,5) split metric is symmetric, involutive, det=-1")


def brillouin_audit() -> None:
    twist = sp.Matrix([[0, -1], [1, 0]])
    glide = sp.diag(1, -1)
    assert twist * twist == -sp.eye(2)
    assert glide * glide == sp.eye(2)
    assert_zero_matrix(glide * twist + twist * glide, "Brillouin glide/twist anticommutator")

    x11, x12, x21, x22 = sp.symbols("x11 x12 x21 x22")
    x = sp.Matrix([[x11, x12], [x21, x22]])
    assert_zero_matrix(glide * (twist * x) + twist * (glide * x), "K(TX) + T(KX)")
    print("PASS: Brillouin Klein-bottle twist/glide laws")


def color_generators() -> list[sp.Matrix]:
    e12 = sp.Matrix([[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    e21 = sp.Matrix([[0, 0, 0], [1, 0, 0], [0, 0, 0]])
    e23 = sp.Matrix([[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    e32 = sp.Matrix([[0, 0, 0], [0, 0, 0], [0, 1, 0]])
    e13 = sp.Matrix([[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    e31 = sp.Matrix([[0, 0, 0], [0, 0, 0], [1, 0, 0]])
    h1 = sp.diag(1, -1, 0)
    h2 = sp.diag(0, 1, -1)
    return [e12, e21, e23, e32, e13, e31, h1, h2]


def color_darkness_audit() -> None:
    gens = color_generators()
    scalar_laser = 2 * sp.eye(3)
    for idx, gen in enumerate(gens):
        assert sp.trace(gen) == 0, idx
        assert_zero_matrix(mat_comm(scalar_laser, gen), f"color generator {idx} dark commutator")

    assert_zero_matrix(mat_comm(gens[0], gens[2]) - gens[4], "[E12,E23] - E13")
    assert_zero_matrix(mat_comm(gens[1], gens[3]) + gens[5], "[E21,E32] + E31")
    print("PASS: rational sl3 color shadow commutes with scalar modular laser")


def main() -> None:
    print("=== Holographic Souriau Reconstruction SymPy audit ===")
    o55_audit()
    brillouin_audit()
    color_darkness_audit()
    print("HOLOGRAPHIC_SOURIAU_RECONSTRUCTION_SYMPY_AUDIT_OK")


if __name__ == "__main__":
    main()
