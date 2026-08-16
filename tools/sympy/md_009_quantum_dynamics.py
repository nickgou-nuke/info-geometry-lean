#!/usr/bin/env python3
"""Finite witness for MD 009 quantum-dynamics algebra.

Mirrors `InfoGeometry.Physics.MD009QuantumDynamics`.

Verified theorem-safe content only:
* normalized Pauli completeness used by the matrix CCR coefficient;
* finite transport of a vector CCR Kronecker table through Pauli soldering
  coefficients;
* quaternion-derivative convention readouts D_q q = 2, D'_q q = 4, and
  (1/2)D_q q = 1.

No PDE, Hilbert-space, self-adjointness, unitary exponential, Schrödinger,
Heisenberg, translation semigroup, propagator, or path-integral theorem is
claimed.
"""

from __future__ import annotations

import itertools
import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_zero


def delta(i: int, j: int) -> int:
    return 1 if i == j else 0


def main() -> int:
    print("=" * 72)
    print("MD 009 FINITE QUANTUM DYNAMICS ALGEBRA")
    print("=" * 72)

    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    sigma = [I2, s1, s2, s3]
    c2 = sp.Rational(1, 2)
    ihbar = sp.symbols("ihbar")

    for A, Ap, B, Bp in itertools.product(range(2), repeat=4):
        lhs = sum(c2 * sigma[a][A, Ap] * sigma[a][Bp, B] for a in range(4))
        rhs = delta(A, B) * delta(Ap, Bp)
        assert_zero(lhs - rhs, f"Pauli completeness {(A, Ap, B, Bp)}")
    print("normalized Pauli completeness: OK")

    for A, Ap, B, Bp in itertools.product(range(2), repeat=4):
        lhs = sum(
            c2 * sigma[a][A, Ap] * sigma[b][Bp, B] * ihbar * delta(a, b)
            for a in range(4)
            for b in range(4)
        )
        rhs = ihbar * delta(A, B) * delta(Ap, Bp)
        assert_zero(lhs - rhs, f"matrix CCR coefficient {(A, Ap, B, Bp)}")
    print("matrix CCR coefficient transport: OK")

    qsq = [1, -1, -1, -1]
    standard = sp.Rational(1, 2) * (qsq[0] - qsq[1] - qsq[2] - qsq[3])
    unscaled = qsq[0] - qsq[1] - qsq[2] - qsq[3]
    canonical = sp.Rational(1, 2) * standard
    assert_zero(standard - 2, "standard D_q q")
    assert_zero(unscaled - 4, "unscaled D'_q q")
    assert_zero(canonical - 1, "canonically scaled D_q q")
    print("quaternion derivative normalization factors: OK")

    print("=" * 72)
    print("MD 009 FINITE QUANTUM DYNAMICS ALGEBRA VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
