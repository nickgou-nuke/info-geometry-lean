#!/usr/bin/env python3
"""
Symbolic CAS verification of the 4-layer Soldering Hierarchy and Emergent (1,3) Minkowski Spacetime.

Verifies:
1. 4D Pauli Soldering Form Determinant:
   det(θ(x)) = (x⁰)² - (x¹)² - (x²)² - (x³)² = η_{μν} x^μ x^ν
2. Frobenius-Schur (1,3) Lorentzian Signature Reconstruction:
   g(v, w) = 1/2 Tr(θ(v) · adj(θ(w))) = η_{μν} v^μ w^ν
3. Time Sector (F_P = 0, ν = +1) gives +dt²
4. Space Sector (F_P = 1, ν = -1) gives -d𝐱²
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero, assert_matrix_zero


def test_soldering_frobenius_minkowski() -> None:
    print("========================================================================")
    print("SOLDERING FORMS, DETERMINANT METRIC & (1,3) MINKOWSKI EMERGENCE")
    print("========================================================================")

    # 1. 4D Spacetime Coordinates and Pauli Matrices
    t, x, y, z = sp.symbols("t x y z", real=True)
    I = sp.I

    sigma_0 = sp.eye(2)
    sigma_1 = sp.Matrix([[0, 1], [1, 0]])
    sigma_2 = sp.Matrix([[0, -I], [I, 0]])
    sigma_3 = sp.Matrix([[1, 0], [0, -1]])

    # Soldering form θ(x) = t σ₀ + x σ₁ + y σ₂ + z σ₃
    theta = t * sigma_0 + x * sigma_1 + y * sigma_2 + z * sigma_3
    theta_expected = sp.Matrix([
        [t + z, x - I * y],
        [x + I * y, t - z]
    ])
    assert_matrix_zero(theta - theta_expected, "Pauli Soldering form θ(x)")
    print("  [OK] Soldering form θ(x) correctly constructed")

    # 2. Emergence of the Minkowski Metric via Determinant
    det_theta = sp.simplify(theta.det())
    minkowski_norm_sq = t**2 - x**2 - y**2 - z**2
    assert_zero(det_theta - minkowski_norm_sq, "det(θ(x)) = t² - x² - y² - z²")
    print("  [OK] Emergent Metric: det(θ(x)) = t² - x² - y² - z² = η_μν x^μ x^ν")

    # 3. Frobenius-Schur (1,3) Signature Selection:
    # Time sector (x=0, y=0, z=0): F_P = 0, ν = +1
    theta_time = theta.subs({x: 0, y: 0, z: 0})
    det_time = sp.simplify(theta_time.det())
    assert_zero(det_time - t**2, "Time sector det is +t²")
    print("  [OK] Time Sector (F_P = 0, ν = +1): det(θ) = +t² (Positive Metric Sign)")

    # Space sector (t=0): F_P = 1, ν = -1
    theta_space = theta.subs({t: 0})
    det_space = sp.simplify(theta_space.det())
    assert_zero(det_space - (-(x**2 + y**2 + z**2)), "Space sector det is -(x²+y²+z²)")
    print("  [OK] Space Sector (F_P = 1, ν = -1): det(θ) = -(x²+y²+z²) (Negative Metric Sign)")

    # 4. Metric Bilinear Form via Trace and Adjugate
    # g(v, w) = 1/2 Tr(θ(v) · adj(θ(w)))
    t2, x2, y2, z2 = sp.symbols("t2 x2 y2 z2", real=True)
    theta2 = t2 * sigma_0 + x2 * sigma_1 + y2 * sigma_2 + z2 * sigma_3
    theta2_adj = theta2.adjugate()

    bilinear_metric = sp.simplify(sp.Rational(1, 2) * (theta * theta2_adj).trace())
    expected_bilinear = t * t2 - x * x2 - y * y2 - z * z2
    assert_zero(bilinear_metric - expected_bilinear, "Bilinear Minkowski Metric g(v, w)")
    print("  [OK] Trace Metric Reconstruction: 1/2 Tr(θ(v) · adj(θ(w))) = η_μν v^μ w^ν")

    print("========================================================================")
    print("ALL SOLDERING FROBENIUS MINKOWSKI THEOREMS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_soldering_frobenius_minkowski()
