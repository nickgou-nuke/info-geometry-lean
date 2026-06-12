#!/usr/bin/env python3
"""
Finite quaternion Cartan-decomposition matrix witness.

This mirrors lean/InfoGeometry/Canonical/CartanInvolution.lean at the
level of explicit 4x4 complex matrices. It is only a finite matrix witness:
no universal Clifford-algebra isomorphism, full Cartan decomposition theorem,
or bundle-level embedding is claimed.
"""

from __future__ import annotations

import sympy as sp


I = sp.I


def mat(data):
    return sp.Matrix(data)


gamma1 = mat(
    [
        [0, 0, 0, 1],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [-1, 0, 0, 0],
    ]
)

gamma2 = mat(
    [
        [0, 0, 0, -I],
        [0, 0, I, 0],
        [0, I, 0, 0],
        [-I, 0, 0, 0],
    ]
)

gamma3 = mat(
    [
        [0, 0, 1, 0],
        [0, 0, 0, -1],
        [-1, 0, 0, 0],
        [0, 1, 0, 0],
    ]
)

embed_i = gamma1 * gamma2
embed_j = gamma2 * gamma3
embed_k = gamma3 * gamma1


def assert_matrix_eq(lhs, rhs, label: str):
    diff = sp.simplify(lhs - rhs)
    if diff != sp.zeros(*lhs.shape):
        raise AssertionError(f"{label} failed:\n{sp.expand(diff)}")


def main() -> None:
    print("=" * 72)
    print("QUATERNION CARTAN DECOMPOSITION -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    assert_matrix_eq(embed_i * embed_j, embed_k, "embed_i * embed_j = embed_k")
    assert_matrix_eq(embed_j * embed_k, embed_i, "embed_j * embed_k = embed_i")
    assert_matrix_eq(embed_k * embed_i, embed_j, "embed_k * embed_i = embed_j")
    print("  cyclic quaternion products verified")

    assert_matrix_eq(embed_j * embed_i, -embed_k, "embed_j * embed_i = -embed_k")
    assert_matrix_eq(embed_k * embed_j, -embed_i, "embed_k * embed_j = -embed_i")
    assert_matrix_eq(embed_i * embed_k, -embed_j, "embed_i * embed_k = -embed_j")
    print("  reversed quaternion products verified")

    assert_matrix_eq(embed_i * embed_i, -sp.eye(4), "embed_i^2 = -I")
    assert_matrix_eq(embed_j * embed_j, -sp.eye(4), "embed_j^2 = -I")
    assert_matrix_eq(embed_k * embed_k, -sp.eye(4), "embed_k^2 = -I")
    print("  quaternion square laws verified")

    assert_matrix_eq((embed_i * embed_j) * embed_k, -sp.eye(4), "embed_i*embed_j*embed_k = -I")
    print("  quaternion triple product verified")

    print("=" * 72)
    print("QUATERNION CARTAN DECOMPOSITION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
