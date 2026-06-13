#!/usr/bin/env python3
"""Section 02 codebase-grounded finite fundamental-structures verifier.

Mirrors the owner-rebased `InfoGeometry.Section2` finite theorem surface.

Owner alignment:
- Section00/Section30 Pauli square/product and determinant/Minkowski readouts;
- Section01 Pauli coordinate-basis reconstruction context;
- BiQuaternionKahlerFinite R4 complex structures I4c/J4c/K4c.

Closed finite checks here:
- Pauli square and anticommutation identities;
- owner R4 complex structures satisfy quaternion relations;
- those structures preserve the Euclidean/Hilbert-Schmidt coefficient metric;
- the Section30 Pauli spacetime determinant gives the Minkowski readback;
- the Section00 normalized `-2 det(X)` convention gives the vector interval;
- ordinary Hamilton quaternion norm is fenced off from the Minkowski sign.

Not claimed:
- full hyperkahler manifold theorem;
- Nijenhuis tensor for a smooth manifold;
- spinor-bundle soldering;
- smooth/topological equivalence of vector, matrix, and quaternion models.
- ordinary Hamilton `q q*` as a Minkowski metric.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_zero(expr: sp.Expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    print("=== Section 02 codebase-grounded finite fundamental structures ===")

    eye2 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_zero(sigma1**2 - eye2, "sigma1 square")
    assert_matrix_zero(sigma2**2 - eye2, "sigma2 square")
    assert_matrix_zero(sigma3**2 - eye2, "sigma3 square")
    assert_matrix_zero(sigma1 * sigma2 + sigma2 * sigma1, "sigma1/sigma2 anticomm")
    assert_matrix_zero(sigma2 * sigma3 + sigma3 * sigma2, "sigma2/sigma3 anticomm")
    assert_matrix_zero(sigma3 * sigma1 + sigma1 * sigma3, "sigma3/sigma1 anticomm")
    assert_matrix_zero(sigma1 * sigma2 - sp.I * sigma3, "Section30 sigma1 sigma2 product")
    assert_matrix_zero(sigma2 * sigma3 - sp.I * sigma1, "Section30 sigma2 sigma3 product")
    assert_matrix_zero(sigma3 * sigma1 - sp.I * sigma2, "Section30 sigma3 sigma1 product")
    print("Section00/Section30 Pauli square/product/anticommutation identities: OK")

    eye4 = sp.eye(4)
    complex_I = sp.Matrix([[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]])
    complex_J = sp.Matrix([[0, 0, -1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, -1, 0, 0]])
    complex_K = sp.Matrix([[0, 0, 0, -1], [0, 0, -1, 0], [0, 1, 0, 0], [1, 0, 0, 0]])

    assert_matrix_zero(complex_I**2 + eye4, "I^2 = -Id")
    assert_matrix_zero(complex_J**2 + eye4, "J^2 = -Id")
    assert_matrix_zero(complex_K**2 + eye4, "K^2 = -Id")
    assert_matrix_zero(complex_I * complex_J - complex_K, "IJ = K")
    assert_matrix_zero(complex_J * complex_K - complex_I, "JK = I")
    assert_matrix_zero(complex_K * complex_I - complex_J, "KI = J")
    assert_matrix_zero(complex_J * complex_I + complex_K, "JI = -K")
    assert_matrix_zero(complex_K * complex_J + complex_I, "KJ = -I")
    assert_matrix_zero(complex_I * complex_K + complex_J, "IK = -J")
    print("BiQuaternionKahlerFinite R4 quaternion relations: OK")

    for name, op in {"I": complex_I, "J": complex_J, "K": complex_K}.items():
        assert_matrix_zero(op.T * op - eye4, f"{name} orthogonal")
    print("Hilbert-Schmidt coefficient metric preservation: OK")

    t, x, y, z = sp.symbols("t x y z", real=True)
    X = t * eye2 + x * sigma1 + y * sigma2 + z * sigma3
    vector_interval = -t**2 + x**2 + y**2 + z**2
    assert_zero(X.det() - (t**2 - x**2 - y**2 - z**2), "Pauli determinant")
    assert_zero(-X.det() - vector_interval, "Minkowski readback")
    X_normalized = X / sp.sqrt(2)
    assert_zero(-2 * X_normalized.det() - vector_interval, "normalized -2 det readback")
    print("Section00/Section30 Pauli determinant/Minkowski readbacks: OK")

    ordinary_quaternion_norm_spatial_unit = 0**2 + 1**2 + 0**2 + 0**2
    minkowski_spatial_unit = -(0**2) + 1**2 + 0**2 + 0**2
    pauli_bridge_q_spatial_unit = 0**2 - 1**2 - 0**2 - 0**2
    if ordinary_quaternion_norm_spatial_unit != 1:
        raise AssertionError("ordinary quaternion norm spatial unit failed")
    if pauli_bridge_q_spatial_unit != -1:
        raise AssertionError("PauliParavectorBridge q spatial unit failed")
    assert_zero(minkowski_spatial_unit - vector_interval.subs({t: 0, x: 1, y: 0, z: 0}),
                "vector interval spatial unit")
    print("Ordinary quaternion norm sign boundary: OK")

    print("[SUCCESS] Section 02 codebase-grounded finite structures verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
