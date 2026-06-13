#!/usr/bin/env python3
"""Section 00 codebase-grounded finite matrix-basis verifier.

Mirrors `InfoGeometry.Physics.Section00MatrixBasisFramework`.

Owner alignment:
- `Canonical.BiQuaternionKahlerFinite`: R4 complex structures I4c/J4c/K4c;
- `Physics.Section30UnifiedMatrixFramework`: Pauli matrices and determinant;
- `Geometry.PauliParavectorBridge`: same (+,-,-,-) determinant readout.

Not claimed:
- full hyperkaehler manifold structure;
- spinor-bundle/tangent-bundle soldering isomorphism;
- continuum curvature or quantum-gravity emergence.
- ordinary Hamilton quaternion norm as a Minkowski metric.
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
    print("=== Section 00 codebase-grounded finite matrix-basis framework ===")

    I4 = sp.eye(4)
    # Same matrices as Canonical.BiQuaternionKahlerFinite.I4c/J4c/K4c.
    I4c = sp.Matrix(
        [
            [0, -1, 0, 0],
            [1, 0, 0, 0],
            [0, 0, 0, -1],
            [0, 0, 1, 0],
        ]
    )
    J4c = sp.Matrix(
        [
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [1, 0, 0, 0],
            [0, -1, 0, 0],
        ]
    )
    K4c = sp.Matrix(
        [
            [0, 0, 0, -1],
            [0, 0, -1, 0],
            [0, 1, 0, 0],
            [1, 0, 0, 0],
        ]
    )

    assert_matrix_zero(I4c**2 + I4, "owner I4c^2 = -Id")
    assert_matrix_zero(J4c**2 + I4, "owner J4c^2 = -Id")
    assert_matrix_zero(K4c**2 + I4, "owner K4c^2 = -Id")
    assert_matrix_zero(I4c * J4c - K4c, "owner I4c J4c = K4c")
    assert_matrix_zero(J4c * K4c - I4c, "owner J4c K4c = I4c")
    assert_matrix_zero(K4c * I4c - J4c, "owner K4c I4c = J4c")
    assert_matrix_zero(J4c * I4c + K4c, "owner J4c I4c = -K4c")
    assert_matrix_zero(K4c * J4c + I4c, "owner K4c J4c = -I4c")
    assert_matrix_zero(I4c * K4c + J4c, "owner I4c K4c = -J4c")
    print("BiQuaternionKahlerFinite R4 quaternion relations: OK")

    metric = sp.eye(4)
    for name, operator in {"I4c": I4c, "J4c": J4c, "K4c": K4c}.items():
        assert_matrix_zero(operator.T * metric * operator - metric, f"{name} metric preservation")
    print("Hilbert-Schmidt metric preservation: OK")

    t, x, y, z = sp.symbols("t x y z", real=True)
    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    M = t * sigma0 + x * sigma1 + y * sigma2 + z * sigma3

    section30_det = t**2 - x**2 - y**2 - z**2
    section30_minkowski = -t**2 + x**2 + y**2 + z**2
    assert_zero(M.det() - section30_det, "Section30 spacetimeMatrix determinant")
    assert_zero(-M.det() - section30_minkowski, "Section30 (-,+,+,+) readout")
    print("Section30 Pauli determinant/Minkowski readout: OK")

    normalized = M / sp.sqrt(2)
    assert_zero(-2 * normalized.det() - section30_minkowski,
                "derived normalized determinant/Minkowski readout")
    print("Derived normalized determinant readout: OK")

    geometry_q = t**2 - x**2 - y**2 - z**2
    assert_zero(M.det() - geometry_q, "PauliParavectorBridge (+,-,-,-) q readout")
    print("PauliParavectorBridge determinant convention: OK")

    ordinary_quaternion_norm = t**2 + x**2 + y**2 + z**2
    assert_zero(ordinary_quaternion_norm.subs({t: 0, x: 1, y: 0, z: 0}) - 1,
                "ordinary Hamilton quaternion norm at spatial unit")
    assert_zero(geometry_q.subs({t: 0, x: 1, y: 0, z: 0}) + 1,
                "Minkowski/Pauli readout at spatial unit")
    print("Ordinary quaternion norm sign boundary: OK")

    print("[SUCCESS] Section 00 codebase-grounded finite identities verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
