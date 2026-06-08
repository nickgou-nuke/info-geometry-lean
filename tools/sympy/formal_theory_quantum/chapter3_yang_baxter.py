#!/usr/bin/env python3
"""Chapter 3 companion: Yang-Baxter equation for the finite R-matrix."""

from __future__ import annotations

import sympy as sp

from common import check, kron, mat_eq, universal_R_fundamental


def run() -> None:
    print("Chapter 3: Yang-Baxter finite shadow")
    q = sp.symbols("q", nonzero=True)
    I = sp.eye(2)
    R = universal_R_fundamental(q)
    swap = sp.Matrix(
        [
            [1, 0, 0, 0],
            [0, 0, 1, 0],
            [0, 1, 0, 0],
            [0, 0, 0, 1],
        ]
    )

    R12 = kron(R, I)
    R23 = kron(I, R)
    P23 = kron(I, swap)
    R13 = P23 * R12 * P23

    check("R12 R13 R23 = R23 R13 R12", mat_eq(R12 * R13 * R23, R23 * R13 * R12))


if __name__ == "__main__":
    run()
