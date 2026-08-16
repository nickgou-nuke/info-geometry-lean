#!/usr/bin/env python3
"""Coordinate-free connection channel checks.

This is the concrete SymPy companion to
``lean/InfoGeometry/Canonical/CoordinateFreeConnectionChannels.lean``.

The Lean file is the proof authority.  This script instantiates the abstract
ring-hom channel laws with matrix representation channels:

* spinor channel: identity representation;
* vector channel: ``A -> I_2 kron A``;
* quaternion channel: ``A -> A kron I_2``.

No external certificate is consumed.  The identities are derived by exact
symbolic matrix algebra.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero as _assert_matrix_zero, comm as commutator


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    _assert_matrix_zero(matrix, name)
    print(f"  {name}: OK")


def two_slot_curvature(
    d_xy: sp.Matrix,
    d_yx: sp.Matrix,
    a_x: sp.Matrix,
    a_y: sp.Matrix,
) -> sp.Matrix:
    return d_xy - d_yx + commutator(a_x, a_y)


def spinor_channel(a: sp.Matrix) -> sp.Matrix:
    return a


def vector_channel(a: sp.Matrix) -> sp.Matrix:
    return sp.kronecker_product(sp.eye(2), a)


def quaternion_channel(a: sp.Matrix) -> sp.Matrix:
    return sp.kronecker_product(a, sp.eye(2))


def symbolic_matrix(prefix: str, n: int) -> sp.Matrix:
    return sp.Matrix(n, n, sp.symbols(f"{prefix}0:{n*n}"))


def verify_channel(name: str, channel, n: int) -> None:
    print(f"\n{name} channel")
    d_xy = symbolic_matrix(f"{name}_dxy_", n)
    d_yx = symbolic_matrix(f"{name}_dyx_", n)
    a_x = symbolic_matrix(f"{name}_ax_", n)
    a_y = symbolic_matrix(f"{name}_ay_", n)

    base_curv = two_slot_curvature(d_xy, d_yx, a_x, a_y)
    image_curv = two_slot_curvature(channel(d_xy), channel(d_yx), channel(a_x), channel(a_y))
    assert_matrix_zero("channel preserves curvature", channel(base_curv) - image_curv)

    base_comm = commutator(a_x, a_y)
    image_comm = commutator(channel(a_x), channel(a_y))
    assert_matrix_zero("channel preserves commutator", channel(base_comm) - image_comm)

    swapped = two_slot_curvature(channel(d_yx), channel(d_xy), channel(a_y), channel(a_x))
    assert_matrix_zero("image curvature is antisymmetric", image_curv + swapped)


def verify_bianchi_preservation() -> None:
    print("\ncyclic Bianchi preservation")
    x = symbolic_matrix("bianchi_x_", 2)
    y = symbolic_matrix("bianchi_y_", 2)
    z = -x - y
    for name, channel in (
        ("spinor", spinor_channel),
        ("vector", vector_channel),
        ("quaternion", quaternion_channel),
    ):
        assert_matrix_zero(f"{name}: channel(X+Y+Z)=0",
                           channel(x) + channel(y) + channel(z))


def verify_trifactor_transport() -> None:
    print("\ntrifactor-law transport")
    t = sp.diag(1, -1, 0)
    assert_matrix_zero("base T^3 - T = 0", t**3 - t)
    for name, channel in (
        ("spinor", spinor_channel),
        ("vector", vector_channel),
        ("quaternion", quaternion_channel),
    ):
        image_t = channel(t)
        assert_matrix_zero(f"{name}: image(T)^3 - image(T) = 0", image_t**3 - image_t)


def main() -> int:
    print("=" * 72)
    print("COORDINATE-FREE CONNECTION CHANNELS")
    print("=" * 72)

    verify_channel("spinor", spinor_channel, 2)
    verify_channel("vector", vector_channel, 2)
    verify_channel("quaternion", quaternion_channel, 2)
    verify_bianchi_preservation()
    verify_trifactor_transport()

    print("\nCOORDINATE-FREE CHANNELS VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
