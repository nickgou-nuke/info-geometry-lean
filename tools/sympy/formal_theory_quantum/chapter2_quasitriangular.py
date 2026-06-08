#!/usr/bin/env python3
"""Chapter 2 companion: finite quasitriangular intertwining law.

This file uses the right-handed finite convention for the chosen fundamental
R-matrix:

    Delta(x) R = R Delta^op(x)

The transposed/inverse convention is equivalent after changing which universal
R orientation is named `R`.  The scripts keep one convention fixed so Chapters
2-4 share the same finite matrix.
"""

from __future__ import annotations

import sympy as sp

from common import check, fundamental_uqsl2, kron, mat_eq, universal_R_fundamental


def opposite_delta(delta_x: sp.Matrix) -> sp.Matrix:
    # Swap the two tensor factors in the 2x2 fundamental tensor square.
    swap = sp.Matrix(
        [
            [1, 0, 0, 0],
            [0, 0, 1, 0],
            [0, 1, 0, 0],
            [0, 0, 0, 1],
        ]
    )
    return swap * delta_x * swap


def run() -> None:
    print("Chapter 2: quasitriangular finite shadow")
    q = sp.symbols("q", nonzero=True)
    E, F, K, Kinv = fundamental_uqsl2(q)
    I = sp.eye(2)
    R = universal_R_fundamental(q)

    # One standard Drinfeld-Jimbo convention on the fundamental module.
    delta_E = kron(E, K) + kron(I, E)
    delta_F = kron(F, I) + kron(Kinv, F)
    delta_K = kron(K, K)

    check("Delta(E) R = R Delta^op(E)", mat_eq(delta_E * R, R * opposite_delta(delta_E)))
    check("Delta(F) R = R Delta^op(F)", mat_eq(delta_F * R, R * opposite_delta(delta_F)))
    check("Delta(K) R = R Delta^op(K)", mat_eq(delta_K * R, R * opposite_delta(delta_K)))
    check("R is invertible in finite shadow", R.det() != 0)


if __name__ == "__main__":
    run()
