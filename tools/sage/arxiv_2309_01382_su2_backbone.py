#!/usr/bin/env python3
"""Sage exact algebraic backbone for arXiv:2309.01382v1.

Run with:
    /home/goutev/miniforge3/envs/sage/bin/python tools/sage/arxiv_2309_01382_su2_backbone.py
"""

from __future__ import annotations

from sage.all import Matrix, QQ, identity_matrix, zero_matrix


def main() -> None:
    Jp = Matrix(QQ, [[0, 1], [0, 0]])
    Jm = Matrix(QQ, [[0, 0], [1, 0]])
    J0 = Matrix(QQ, [[QQ(1) / 2, 0], [0, -QQ(1) / 2]])

    comm = lambda A, B: A * B - B * A
    assert comm(Jp, Jm) == 2 * J0
    assert comm(J0, Jp) == Jp
    assert comm(J0, Jm) == -Jm

    up = Matrix(QQ, [[1], [0]])
    down = Matrix(QQ, [[0], [1]])
    assert Jp * up == zero_matrix(QQ, 2, 1)
    assert Jp * down == up
    assert Jm * up == down
    assert Jm * down == zero_matrix(QQ, 2, 1)

    casimir = J0 * J0 + QQ(1) / 2 * (Jp * Jm + Jm * Jp)
    assert casimir == QQ(3) / 4 * identity_matrix(QQ, 2)

    E = QQ(0)
    H = Matrix(QQ, [[E, 0], [0, E]])
    assert H == zero_matrix(QQ, 2)

    parity = Matrix(QQ, [[1, 0], [0, -1]])
    assert (parity * identity_matrix(QQ, 2)).trace() == 0
    P = Matrix(QQ, [[0, 1], [1, 0]])
    assert P * P == identity_matrix(QQ, 2)

    print("ARXIV_2309_01382_SAGE_SU2_BACKBONE_OK")
    print("field=QQ")
    print("casimir=3/4")


if __name__ == "__main__":
    main()
