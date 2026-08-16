#!/usr/bin/env python3
"""Finite unified matrix quantum-geometry checks.

Mirrors `InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite`.

Closed scope:
* Pauli square/product/trace identities;
* the quaternion sign obstruction for `k -> i sigma3`, and the corrected
  homomorphic basis `k -> -i sigma3`;
* Hermitian Pauli-point determinant and Minkowski readback;
* Bloch density determinant and unit-Bloch pure determinant;
* finite von-Neumann commutator as Bloch precession.

No continuum geometry, Einstein equation, entanglement area law, CP1
diffeomorphism, or physical quantum-gravity dynamics is claimed here.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, pauli_matrices


def main() -> int:
    print("=" * 72)
    print("FINITE UNIFIED MATRIX QUANTUM GEOMETRY")
    print("=" * 72)

    eye = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_zero(sigma1**2 - eye, "sigma1 square")
    assert_matrix_zero(sigma2**2 - eye, "sigma2 square")
    assert_matrix_zero(sigma3**2 - eye, "sigma3 square")
    assert_matrix_zero(sigma1 * sigma2 - sp.I * sigma3, "sigma1 sigma2")
    assert_matrix_zero(sigma2 * sigma3 - sp.I * sigma1, "sigma2 sigma3")
    assert_matrix_zero(sigma3 * sigma1 - sp.I * sigma2, "sigma3 sigma1")
    assert_zero(sp.trace(sigma1), "trace sigma1")
    assert_zero(sp.trace(sigma2), "trace sigma2")
    assert_zero(sp.trace(sigma3), "trace sigma3")
    print("  Pauli products and traces verified")

    literal_k = sp.I * sigma3
    corrected_i = sp.I * sigma1
    corrected_j = sp.I * sigma2
    corrected_k = -sp.I * sigma3
    assert_matrix_zero(corrected_i * corrected_j + literal_k, "literal k sign obstruction")
    assert_matrix_zero(corrected_i**2 + eye, "qI square")
    assert_matrix_zero(corrected_j**2 + eye, "qJ square")
    assert_matrix_zero(corrected_k**2 + eye, "qK square")
    assert_matrix_zero(corrected_i * corrected_j - corrected_k, "qI qJ = qK")
    assert_matrix_zero(corrected_j * corrected_k - corrected_i, "qJ qK = qI")
    assert_matrix_zero(corrected_k * corrected_i - corrected_j, "qK qI = qJ")
    print("  quaternion sign correction and multiplication table verified")

    t, x, y, z = sp.symbols("t x y z")
    point = sp.Matrix([[t + z, x - sp.I * y], [x + sp.I * y, t - z]])
    det_point = sp.expand(point.det())
    assert_zero(det_point - (t**2 - x**2 - y**2 - z**2), "Pauli-point determinant")
    normalized_det = sp.Rational(1, 2) * det_point
    assert_zero(
        -2 * normalized_det - (-t**2 + x**2 + y**2 + z**2),
        "Minkowski readback",
    )
    print("  Hermitian Pauli-point determinant verified")

    n1, n2, n3 = sp.symbols("n1 n2 n3")
    rho = sp.Matrix(
        [
            [(1 + n3) / 2, (n1 - sp.I * n2) / 2],
            [(n1 + sp.I * n2) / 2, (1 - n3) / 2],
        ]
    )
    assert_zero(
        rho.det() - sp.Rational(1, 4) * (1 - (n1**2 + n2**2 + n3**2)),
        "density determinant",
    )
    unit_sub = {n3**2: 1 - n1**2 - n2**2}
    assert_zero(rho.det().subs(unit_sub), "unit Bloch determinant")
    print("  density determinant and pure finite shadow verified")

    w1, w2, w3 = sp.symbols("w1 w2 w3")
    ham = sp.Matrix(
        [
            [w3 / 2, (w1 - sp.I * w2) / 2],
            [(w1 + sp.I * w2) / 2, -w3 / 2],
        ]
    )
    rhs = -sp.I * (ham * rho - rho * ham)
    cross = (
        (w2 * n3 - w3 * n2) * sigma1
        + (w3 * n1 - w1 * n3) * sigma2
        + (w1 * n2 - w2 * n1) * sigma3
    ) / 2
    assert_matrix_zero(rhs - cross, "Bloch precession commutator")
    print("  finite Bloch precession commutator verified")

    print("=" * 72)
    print("FINITE UNIFIED MATRIX QUANTUM GEOMETRY VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
