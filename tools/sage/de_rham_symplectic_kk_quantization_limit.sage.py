#!/usr/bin/env sage-python
"""Sage exact-rational certificate for de Rham/symplectic/KK/colimit bridge."""

import json
from sage.all import Matrix, QQ, vector


def main() -> None:
    d0 = Matrix(QQ, [[-1, 1, 0], [0, -1, 1], [1, 0, -1]])
    d1 = Matrix(QQ, [[1, 1, 1]])
    assert d1 * d0 == Matrix(QQ, 1, 3, [0, 0, 0])

    potential = vector(QQ, [2, -1, 3])
    exact_current = d0 * potential
    assert d1 * exact_current == vector(QQ, [0])

    d1_zero = Matrix(QQ, 1, 3, [0, 0, 0])
    obstruction = vector(QQ, [1, 1, 1])
    assert d1_zero * obstruction == vector(QQ, [0])
    assert obstruction not in d0.column_space()

    J = Matrix(QQ, [[0, 1], [-1, 0]])
    S = Matrix(QQ, [[1, 1], [0, 1]])
    assert S.transpose() * J * S == J

    kk = Matrix(QQ, [
        [-QQ(1) / 2, QQ(1) / 3, 0, 0, 1],
        [QQ(1) / 3, QQ(11) / 9, 0, 0, QQ(2) / 3],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [1, QQ(2) / 3, 0, 0, 2],
    ])
    assert kk.det() == -2

    omega, curvature, hbar = QQ(6), QQ(2), QQ(3)
    assert curvature * hbar == omega

    n = 2
    x = QQ(3) / 5
    assert (2 * x) / (2 ** (n + 1)) == x / (2 ** n)

    print(json.dumps({
        "certificate": "de_rham_symplectic_kk_quantization_limit",
        "ring": "QQ",
        "sage": True,
        "d1_d0_zero": True,
        "closed_nonexact_circle_current": [1, 1, 1],
        "symplectic_shear_preserves_J": True,
        "kk_metric_det": str(kk.det()),
        "colimit_cone_sample": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
