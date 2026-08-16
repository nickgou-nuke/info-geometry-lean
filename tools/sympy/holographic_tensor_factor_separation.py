#!/usr/bin/env python3
"""Exact-rational SymPy certificate for holographic tensor-factor separation."""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, comm

assert_zero_matrix = assert_matrix_zero


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


def geometric_generators() -> list[sp.Matrix]:
    eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
    parity = -sp.eye(10)
    b = sp.zeros(5)
    b[0, 1] = sp.Rational(2, 3)
    b[1, 0] = -sp.Rational(2, 3)
    b_transform = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.eye(5), b),
        sp.Matrix.hstack(sp.zeros(5), sp.eye(5)),
    )
    return [eta, parity, b_transform]


def verify_tensor_factorization() -> None:
    i10 = sp.eye(10)
    i3 = sp.eye(3)
    for g_idx, geom in enumerate(geometric_generators()):
        geom_lift = sp.kronecker_product(geom, i3)
        for c_idx, color in enumerate(color_generators()):
            color_lift = sp.kronecker_product(i10, color)
            assert_zero_matrix(comm(geom_lift, color_lift), f"G{g_idx} tensor C{c_idx}")
    print("PASS: (G tensor I3) commutes with (I10 tensor C) for finite generators")


def verify_brillouin_confined_factor() -> None:
    i3 = sp.eye(3)
    twist = sp.Matrix([[0, -1], [1, 0]])
    glide = sp.diag(1, -1)
    twist_lift = sp.kronecker_product(twist, i3)
    glide_lift = sp.kronecker_product(glide, i3)
    assert twist_lift * twist_lift == -sp.eye(6)
    assert glide_lift * glide_lift == sp.eye(6)
    assert_zero_matrix(glide_lift * twist_lift + twist_lift * glide_lift, "lifted Brillouin anticommutator")

    i2 = sp.eye(2)
    for idx, color in enumerate(color_generators()):
        color_lift = sp.kronecker_product(i2, color)
        assert_zero_matrix(comm(twist_lift, color_lift), f"twist tensor C{idx}")
        assert_zero_matrix(comm(glide_lift, color_lift), f"glide tensor C{idx}")
    print("PASS: Brillouin twist/glide confined to geometric tensor factor")


def main() -> None:
    print("=== Holographic tensor-factor separation SymPy certificate ===")
    verify_tensor_factorization()
    verify_brillouin_confined_factor()
    print("HOLOGRAPHIC_TENSOR_FACTOR_SEPARATION_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
