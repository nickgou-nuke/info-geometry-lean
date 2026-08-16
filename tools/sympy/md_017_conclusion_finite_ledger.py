#!/usr/bin/env python3
"""Finite witness for MD 017 conclusion ledger.

Mirrors `InfoGeometry.Physics.MD017ConclusionFiniteLedger`.

Chapter 17 is a conclusion/outlook chapter.  This script checks only finite
algebraic ledger items reused from earlier repaired owners:
* Section 17 biquaternion coordinate map and inverse;
* Section 17 bridge to Section 16 coordinates;
* MD013 one-mode CAR projectors partition/orthogonality;
* MD014 Z3 sector projectors partition and trace readouts;
* MD016 scalar equation-of-state sample arithmetic.

No Standard Model, QFT, GR, experimental prediction, anomaly-cancellation, or
emergence theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero

I = sp.I


def assert_tuple_equal(a, b, label: str) -> None:
    for lhs, rhs in zip(a, b):
        assert_zero(lhs - rhs, label)


def biquat_to_matrix(c0, c1, c2, c3):
    return sp.Matrix([[c0 + I * c1, c2 + I * c3], [-c2 + I * c3, c0 - I * c1]])


def matrix_to_biquat(M):
    return (
        (M[0, 0] + M[1, 1]) / 2,
        -I * (M[0, 0] - M[1, 1]) / 2,
        (M[0, 1] - M[1, 0]) / 2,
        -I * (M[0, 1] + M[1, 0]) / 2,
    )


def section16_even_to_matrix(z0, z1, z2, z3):
    return sp.Matrix([[z0 - I * z2, I * z1 - z3], [I * z1 + z3, z0 + I * z2]])


def main() -> int:
    print("=" * 72)
    print("MD 017 FINITE CONCLUSION LEDGER")
    print("=" * 72)

    c0, c1, c2, c3 = sp.symbols("c0 c1 c2 c3")
    q = (c0, c1, c2, c3)
    a, b, c, d = sp.symbols("a b c d")
    M = sp.Matrix([[a, b], [c, d]])
    assert_tuple_equal(matrix_to_biquat(biquat_to_matrix(*q)), q, "biquat coordinate right inverse")
    assert_matrix_zero(biquat_to_matrix(*matrix_to_biquat(M)) - M, "biquat matrix left inverse")
    assert_matrix_zero(
        biquat_to_matrix(*q) - section16_even_to_matrix(c0, c3, -c1, -c2),
        "Section17-to-Section16 coordinate bridge",
    )
    print("biquaternion coordinate ledger: OK")

    I2 = sp.eye(2)
    E12 = sp.Matrix([[0, 1], [0, 0]])
    E21 = sp.Matrix([[0, 0], [1, 0]])
    assert_matrix_zero(E12 * E21 + E21 * E12 - I2, "CAR projectors partition identity")
    assert_matrix_zero((E12 * E21) * (E21 * E12), "CAR projectors orthogonal left-right")
    assert_matrix_zero((E21 * E12) * (E12 * E21), "CAR projectors orthogonal right-left")
    print("CAR projector ledger: OK")

    I3 = sp.eye(3)
    P0 = sp.diag(1, 0, 0)
    P1 = sp.diag(0, 1, 0)
    P2 = sp.diag(0, 0, 1)
    assert_matrix_zero(P0 + P1 + P2 - I3, "Z3 projector partition identity")
    assert_zero(sp.trace(P0) - 1, "trace P0")
    assert_zero(sp.trace(P1) - 1, "trace P1")
    assert_zero(sp.trace(P2) - 1, "trace P2")
    print("Z3 projector ledger: OK")

    dark_energy_eos = -1 + sp.Rational(6, 100) / 3
    assert_zero(dark_energy_eos + sp.Rational(98, 100), "MD016 EOS sample")
    print("finite scalar prediction-arithmetic ledger: OK")

    print("=" * 72)
    print("MD 017 FINITE CONCLUSION LEDGER VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
