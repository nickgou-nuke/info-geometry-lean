#!/usr/bin/env python3
"""Sage exact backbone for the dual split-octonion lane.

Run with:
    /home/goutev/miniforge3/envs/sage/bin/python tools/sage/dual_split_octonion_sage_backbone.py

Scope: exact integer/rational linear algebra only.  This does not classify the
automorphism group of the dual split-octonion algebra.
"""

from __future__ import annotations

from sage.all import Matrix, QQ, ZZ, identity_matrix, vector


def check_dual_number_matrix() -> None:
    eps = Matrix(ZZ, [[0, 1], [0, 0]])
    assert eps * eps == Matrix(ZZ, 2, 2, 0)
    assert identity_matrix(ZZ, 2) * eps == eps
    assert eps * identity_matrix(ZZ, 2) == eps


def check_split_signature() -> None:
    gram = Matrix(ZZ, 8, 8, lambda i, j: 0)
    for i in range(4):
        gram[i, i] = 1
    for i in range(4, 8):
        gram[i, i] = -1
    assert gram.det() == 1
    assert gram.rank() == 8
    # A representative null vector in signature (4,4).
    v = vector(ZZ, [1, 0, 0, 0, 1, 0, 0, 0])
    assert (v.row() * gram * v.column())[0, 0] == 0


def check_stage_stability() -> None:
    # The finite-to-indexed readout used by Lean is just constant exact data at
    # every finite stage; no analytic completion is asserted here.
    eps = Matrix(QQ, [[0, 1], [0, 0]])
    stages = [eps * eps for _ in range(8)]
    assert all(M == Matrix(QQ, 2, 2, 0) for M in stages)


def main() -> None:
    check_dual_number_matrix()
    check_split_signature()
    check_stage_stability()
    print("DUAL_SPLIT_OCTONION_SAGE_BACKBONE_OK")
    print("signature_rank=8")
    print("dual_epsilon_square_zero=true")


if __name__ == "__main__":
    main()
