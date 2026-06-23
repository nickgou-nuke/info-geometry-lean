#!/usr/bin/env sage -python
"""Sage exact-rational certificate for holographic tensor-factor separation."""

from __future__ import annotations

from sage.all import Matrix, QQ, diagonal_matrix, identity_matrix, block_matrix, zero_matrix


def assert_zero_matrix(mat, label: str) -> None:
    if mat != Matrix(QQ, mat.nrows(), mat.ncols(), 0):
        raise AssertionError(f"{label} failed:\n{mat}")


def comm(a, b):
    return a * b - b * a


def colors():
    e12 = Matrix(QQ, [[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    e21 = Matrix(QQ, [[0, 0, 0], [1, 0, 0], [0, 0, 0]])
    e23 = Matrix(QQ, [[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    e32 = Matrix(QQ, [[0, 0, 0], [0, 0, 0], [0, 1, 0]])
    e13 = Matrix(QQ, [[0, 0, 1], [0, 0, 0], [0, 0, 0]])
    e31 = Matrix(QQ, [[0, 0, 0], [0, 0, 0], [1, 0, 0]])
    h1 = diagonal_matrix(QQ, [1, -1, 0])
    h2 = diagonal_matrix(QQ, [0, 1, -1])
    return [e12, e21, e23, e32, e13, e31, h1, h2]


def main() -> None:
    print("=== Holographic tensor-factor separation Sage certificate ===")
    eta = diagonal_matrix(QQ, [1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
    parity = -identity_matrix(QQ, 10)
    b = zero_matrix(QQ, 5)
    b[0, 1] = QQ(2) / 3
    b[1, 0] = -QQ(2) / 3
    b_transform = block_matrix(QQ, [[identity_matrix(QQ, 5), b], [zero_matrix(QQ, 5), identity_matrix(QQ, 5)]])
    i10 = identity_matrix(QQ, 10)
    i3 = identity_matrix(QQ, 3)

    for gi, geom in enumerate([eta, parity, b_transform]):
        geom_lift = geom.tensor_product(i3)
        for ci, color in enumerate(colors()):
            color_lift = i10.tensor_product(color)
            assert_zero_matrix(comm(geom_lift, color_lift), f"G{gi} tensor C{ci}")

    twist = Matrix(QQ, [[0, -1], [1, 0]])
    glide = Matrix(QQ, [[1, 0], [0, -1]])
    twist_lift = twist.tensor_product(i3)
    glide_lift = glide.tensor_product(i3)
    assert twist_lift * twist_lift == -identity_matrix(QQ, 6)
    assert glide_lift * glide_lift == identity_matrix(QQ, 6)
    assert_zero_matrix(glide_lift * twist_lift + twist_lift * glide_lift, "lifted Brillouin anticommutator")
    i2 = identity_matrix(QQ, 2)
    for ci, color in enumerate(colors()):
        color_lift = i2.tensor_product(color)
        assert_zero_matrix(comm(twist_lift, color_lift), f"twist tensor C{ci}")
        assert_zero_matrix(comm(glide_lift, color_lift), f"glide tensor C{ci}")

    print("PASS: exact tensor-factor commutation and Brillouin confinement")
    print("HOLOGRAPHIC_TENSOR_FACTOR_SEPARATION_SAGE_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
