#!/usr/bin/env python3
"""Finite partition/covariance witness for MD 20250430070955.

Mirrors `InfoGeometry.Physics.MD20250430070955FinitePartition`.

The source manuscript discusses partition functions, Fisher metrics,
statistical field theory, and emergent spacetime.  This witness verifies only
finite algebraic shadows:
* normalized weights sum to one;
* independent finite partition functions factorize;
* weighted covariance is symmetric;
* a constant observable has zero covariance;
* the previous MD Pauli matrix-statistics recomposition remains valid.
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
    print("MD 20250430070955 FINITE PARTITION/COVARIANCE")
    print("=" * 72)

    # Normalization of a finite partition.
    w0, w1, w2 = sp.symbols("w0 w1 w2", nonzero=True)
    weights = [w0, w1, w2]
    Z = sum(weights)
    normalized = [w / Z for w in weights]
    assert_zero(sum(normalized) - 1, "normalized finite weights sum to one")
    print("normalized weights sum to one: OK")

    # Independent finite subsystem factorization.
    a0, a1, b0, b1, b2 = sp.symbols("a0 a1 b0 b1 b2")
    wa = [a0, a1]
    vb = [b0, b1, b2]
    product_partition = sum(x * y for x in wa for y in vb)
    assert_zero(product_partition - sum(wa) * sum(vb), "finite partition factorization")
    print("independent partition factorization: OK")

    # Covariance symmetry.
    O = sp.symbols("O0 O1 O2")
    P = sp.symbols("P0 P1 P2")
    mean_O = sum(normalized[i] * O[i] for i in range(3))
    mean_P = sum(normalized[i] * P[i] for i in range(3))
    cov_OP = sum(normalized[i] * (O[i] - mean_O) * (P[i] - mean_P) for i in range(3))
    cov_PO = sum(normalized[i] * (P[i] - mean_P) * (O[i] - mean_O) for i in range(3))
    assert_zero(cov_OP - cov_PO, "finite covariance symmetry")
    print("finite covariance symmetry: OK")

    # Constant observable has zero covariance.
    c = sp.symbols("c")
    mean_c = sum(normalized[i] * c for i in range(3))
    cov_cP = sum(normalized[i] * (c - mean_c) * (P[i] - mean_P) for i in range(3))
    assert_zero(cov_cP, "constant observable zero covariance")
    print("constant observable zero covariance: OK")

    # Local 2x2 matrix-statistics readback from the previous MD bridge.
    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    A = mat2("A")
    coeff = pauli_coeffs(A)
    recomposed = sum((coeff[k] * [sigma0, sigma1, sigma2, sigma3][k] for k in range(4)), sp.zeros(2))
    assert_matrix_zero(recomposed - A, "Pauli matrix-statistics recomposition")
    print("Pauli local matrix readback: OK")

    print("=" * 72)
    print("MD 20250430070955 FINITE PARTITION/COVARIANCE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
