#!/usr/bin/env python3
"""Section 01 codebase-grounded finite Pauli-basis verifier.

Mirrors `InfoGeometry.Physics.Section01MatrixBasisIntroduction`.

Owner-backed checks:
- Section00/Section30 Pauli square and product packets;
- canonical finite Pauli trace and determinant readouts;
- Section00 source-normalized spacetime determinant readout;
- Section30 Bloch density trace and determinant readouts;
- every 2x2 complex matrix has explicit Pauli coefficients;
- coefficient readback is inverse to expansion and reconstructs the matrix.

Not claimed:
- quantum-gravity unification;
- entanglement-as-connection;
- evolution-as-translation;
- hyperkaehler manifold geometry;
- spinor/tangent-bundle soldering or continuum curvature.
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
    print("=== Section 01 codebase-grounded finite Pauli-basis introduction ===")

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    assert_matrix_zero(sigma1**2 - sigma0, "Section30 sigma1 square")
    assert_matrix_zero(sigma2**2 - sigma0, "Section30 sigma2 square")
    assert_matrix_zero(sigma3**2 - sigma0, "Section30 sigma3 square")
    assert_matrix_zero(sigma1 * sigma2 - sp.I * sigma3, "Section30 sigma1 sigma2")
    assert_matrix_zero(sigma2 * sigma3 - sp.I * sigma1, "Section30 sigma2 sigma3")
    assert_matrix_zero(sigma3 * sigma1 - sp.I * sigma2, "Section30 sigma3 sigma1")
    assert_zero(sp.trace(sigma1), "canonical trace sigma1")
    assert_zero(sp.trace(sigma2), "canonical trace sigma2")
    assert_zero(sp.trace(sigma3), "canonical trace sigma3")
    print("Owner-backed Pauli square/product/trace packets: OK")

    def expand(a, b, c, d):
        return a * sigma0 + b * sigma1 + c * sigma2 + d * sigma3

    def coeff_t(M):
        return (M[0, 0] + M[1, 1]) / 2

    def coeff_x(M):
        return (M[0, 1] + M[1, 0]) / 2

    def coeff_y(M):
        return sp.I * (M[0, 1] - M[1, 0]) / 2

    def coeff_z(M):
        return (M[0, 0] - M[1, 1]) / 2

    a, b, c, d = sp.symbols("a b c d")
    expanded = expand(a, b, c, d)
    assert_zero(coeff_t(expanded) - a, "coeff_t expansion inverse")
    assert_zero(coeff_x(expanded) - b, "coeff_x expansion inverse")
    assert_zero(coeff_y(expanded) - c, "coeff_y expansion inverse")
    assert_zero(coeff_z(expanded) - d, "coeff_z expansion inverse")
    print("Coefficient readback inverts Pauli expansion: OK")

    m00, m01, m10, m11 = sp.symbols("m00 m01 m10 m11")
    M = sp.Matrix([[m00, m01], [m10, m11]])
    reconstructed = expand(coeff_t(M), coeff_x(M), coeff_y(M), coeff_z(M))
    assert_matrix_zero(reconstructed - M, "Pauli reconstruction")
    print("Every symbolic 2x2 matrix reconstructs from Pauli coefficients: OK")

    t, x, y, z = sp.symbols("t x y z")
    spacetime_matrix = expand(t, x, y, z)
    assert_zero(spacetime_matrix.det() - (t**2 - x**2 - y**2 - z**2),
                "Section30 determinant owner readout")
    assert_zero(-spacetime_matrix.det() - (-t**2 + x**2 + y**2 + z**2),
                "Section30 Minkowski owner readout")
    normalized_spacetime_matrix = spacetime_matrix / sp.sqrt(2)
    assert_zero(
        -2 * normalized_spacetime_matrix.det()
        - (-t**2 + x**2 + y**2 + z**2),
        "Section00 normalized determinant/Minkowski readout",
    )
    print("Owner-backed determinant/Minkowski readouts: OK")

    nx, ny, nz = sp.symbols("nx ny nz", real=True)
    bloch = sp.Rational(1, 2) * (sigma0 + nx * sigma1 + ny * sigma2 + nz * sigma3)
    assert_zero(sp.trace(bloch) - 1, "Section30 Bloch density trace")
    assert_zero(
        bloch.det() - (1 - nx**2 - ny**2 - nz**2) / 4,
        "Section30 Bloch density determinant",
    )
    assert_zero(
        bloch.det().subs({nx: 1, ny: 0, nz: 0}),
        "Section30 unit Bloch boundary determinant",
    )
    print("Owner-backed Bloch density trace/determinant readouts: OK")

    a2, b2, c2, d2 = sp.symbols("a2 b2 c2 d2")
    equality_residual = expand(a, b, c, d) - expand(a2, b2, c2, d2)
    recovered_residuals = [
        coeff_t(equality_residual) - (a - a2),
        coeff_x(equality_residual) - (b - b2),
        coeff_y(equality_residual) - (c - c2),
        coeff_z(equality_residual) - (d - d2),
    ]
    for idx, residual in enumerate(recovered_residuals):
        assert_zero(residual, f"uniqueness residual {idx}")
    print("Coefficient uniqueness residuals: OK")

    print("[SUCCESS] Section 01 codebase-grounded finite Pauli-basis identities verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
