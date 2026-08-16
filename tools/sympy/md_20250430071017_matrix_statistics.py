#!/usr/bin/env python3
"""Finite matrix-valued statistics witness for MD 20250430071017.

Mirrors `InfoGeometry.Physics.MD20250430071017MatrixStatistics`.
Closed finite content only:
* arbitrary 2x2 complex matrices decompose/recompose in the Pauli basis;
* finite weighted means of Pauli coefficient statistics;
* finite weighted covariance is symmetric;
* constant local matrix statistics have zero covariance when weights sum to one.

No smooth-manifold theorem, Einstein equation, Kähler theorem, path integral,
emergent-spacetime theorem, Lorentzian-signature emergence theorem, or physical
arrow-of-time theorem is claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, mat2, pauli_matrices


def pauli_coeffs(A: sp.Matrix) -> list[sp.Expr]:
    return [
        (A[0, 0] + A[1, 1]) / 2,
        (A[0, 1] + A[1, 0]) / 2,
        sp.I / 2 * (A[0, 1] - A[1, 0]),
        (A[0, 0] - A[1, 1]) / 2,
    ]


def main() -> int:
    print("=" * 72)
    print("MD 20250430071017 FINITE MATRIX STATISTICS")
    print("=" * 72)

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    basis = [sigma0, sigma1, sigma2, sigma3]

    A = mat2("A")
    coeff = pauli_coeffs(A)
    recomposed = sum((coeff[k] * basis[k] for k in range(4)), sp.zeros(2))
    assert_matrix_zero(recomposed - A, "Pauli recomposition of local matrix")
    print("Pauli coefficient recomposition: OK")

    # Three-point finite ensemble witness.
    qs = [mat2(f"Q{i}") for i in range(3)]
    w0, w1 = sp.symbols("w0 w1")
    weights = [w0, w1, 1 - w0 - w1]

    coeffs = [pauli_coeffs(Q) for Q in qs]
    means = [sum(weights[i] * coeffs[i][k] for i in range(3)) for k in range(4)]
    centered = [[coeffs[i][k] - means[k] for k in range(4)] for i in range(3)]

    covariance = sp.Matrix(4, 4, lambda a, b: sum(weights[i] * centered[i][a] * centered[i][b] for i in range(3)))
    assert_matrix_zero(covariance - covariance.T, "weighted Pauli covariance symmetry")
    print("weighted covariance symmetry: OK")

    C = mat2("C")
    ccoeff = pauli_coeffs(C)
    const_coeffs = [ccoeff for _ in range(3)]
    const_means = [sum(weights[i] * const_coeffs[i][k] for i in range(3)) for k in range(4)]
    const_centered = [[const_coeffs[i][k] - const_means[k] for k in range(4)] for i in range(3)]
    const_cov = sp.Matrix(4, 4, lambda a, b: sum(weights[i] * const_centered[i][a] * const_centered[i][b] for i in range(3)))
    assert_matrix_zero(const_cov, "constant local statistic zero covariance")
    print("constant-statistic zero covariance: OK")

    print("=" * 72)
    print("MD 20250430071017 FINITE MATRIX STATISTICS VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
