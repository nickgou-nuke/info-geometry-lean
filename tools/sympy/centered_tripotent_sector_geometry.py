#!/usr/bin/env python3
"""Finite verification of centered coordinates + doubled polarization + trifactor sectors.

Honest scope:
- verifies the centered involution s = 1/2 + z and z -> -z numerically/symbolically,
- verifies the doubled real polarization axis K = J ε with K^2 = -I and J K J = -K,
- verifies the tripotent sector projectors for T^3 = T,
- verifies a combined tensor-product model where coordinate/polarization data and
  tripotent sector data commute because they act on different factors.

Out of scope:
- analytic continuation,
- actual zeta-zero claims,
- infinite-dimensional von Neumann standard-form analysis.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def assert_eq(lhs, rhs, label: str) -> None:
    if sp.simplify(lhs - rhs) != 0:
        raise AssertionError(f"{label} failed: {sp.simplify(lhs - rhs)}")


def verify_centered_coordinate() -> None:
    z = sp.symbols("z")
    critical_centered = sp.Rational(1, 2) + z
    critical_centered_reflected = sp.Rational(1, 2) - z

    assert_eq(1 - critical_centered, critical_centered_reflected, "1 - criticalCentered(z) = criticalCentered(-z)")

    s = sp.symbols("s")
    xi = s * (1 - s)
    xi_centered = sp.expand(xi.subs(s, critical_centered))
    xi_centered_reflected = sp.expand(xi.subs(s, critical_centered_reflected))
    assert_eq(xi_centered, xi_centered_reflected, "Xi(z) = Xi(-z) on model xi(s)=s(1-s)")

    print("centered coordinate: z ↦ 1/2 + z and z ↦ -z involution verified")


def verify_doubled_polarization() -> None:
    I2 = sp.eye(2)
    J = sp.Matrix([[0, 1], [1, 0]])
    eps = sp.Matrix([[1, 0], [0, -1]])
    K = J * eps

    assert_matrix_eq(J * J, I2, "J^2 = I")
    assert_matrix_eq(eps * eps, I2, "eps^2 = I")
    assert_matrix_eq(J * eps, -eps * J, "J eps = - eps J")
    assert_matrix_eq(K * K, -I2, "K^2 = -I")
    assert_matrix_eq(J * K * J, -K, "J K J = -K")

    sigma, tau = sp.symbols("sigma tau", real=True)
    centered_hestenes = (sp.Rational(1, 2) + sigma) * I2 + tau * K
    mirrored = J * centered_hestenes * J
    expected = (sp.Rational(1, 2) + sigma) * I2 - tau * K
    assert_matrix_eq(mirrored, expected, "mirror flips only the imaginary/polarization part")

    print("doubled polarization: K = J eps, K^2 = -I, J K J = -K verified")


def verify_trifactor_sectors() -> None:
    T = sp.diag(1, -1, 0)
    I3 = sp.eye(3)
    P_zero = I3 - T**2
    P_plus = (T**2 + T) / 2
    P_minus = (T**2 - T) / 2

    assert_matrix_eq(T**3, T, "T^3 = T")
    assert_matrix_eq(P_zero * P_zero, P_zero, "P_zero^2 = P_zero")
    assert_matrix_eq(P_plus * P_plus, P_plus, "P_plus^2 = P_plus")
    assert_matrix_eq(P_minus * P_minus, P_minus, "P_minus^2 = P_minus")
    assert_matrix_eq(P_plus * P_minus, sp.zeros(3), "P_plus P_minus = 0")
    assert_matrix_eq(P_zero * P_plus, sp.zeros(3), "P_zero P_plus = 0")
    assert_matrix_eq(P_zero * P_minus, sp.zeros(3), "P_zero P_minus = 0")
    assert_matrix_eq(P_zero + P_plus + P_minus, I3, "partition of unity")
    assert_matrix_eq(T * P_zero, sp.zeros(3), "T on boundary sector")
    assert_matrix_eq(T * P_plus, P_plus, "T on flow sector")
    assert_matrix_eq(T * P_minus, -P_minus, "T on mirror sector")

    print("trifactor sectors: boundary / flow / mirror projector laws verified")


def verify_combined_tensor_model() -> None:
    I2 = sp.eye(2)
    J = sp.Matrix([[0, 1], [1, 0]])
    eps = sp.Matrix([[1, 0], [0, -1]])
    K = J * eps

    T = sp.diag(1, -1, 0)
    I3 = sp.eye(3)
    P_zero = I3 - T**2
    P_plus = (T**2 + T) / 2
    P_minus = (T**2 - T) / 2

    sigma, tau = sp.symbols("sigma tau", real=True)
    centered = (sp.Rational(1, 2) + sigma) * I2 + tau * K

    S_zero = sp.kronecker_product(P_zero, centered)
    S_plus = sp.kronecker_product(P_plus, centered)
    S_minus = sp.kronecker_product(P_minus, centered)
    total = S_zero + S_plus + S_minus
    expected_total = sp.kronecker_product(I3, centered)
    assert_matrix_eq(total, expected_total, "sector-resolved centered coordinate recombines")

    T_big = sp.kronecker_product(T, I2)
    assert_matrix_eq(T_big * S_zero, sp.zeros(6), "T kills boundary component")
    assert_matrix_eq(T_big * S_plus, S_plus, "T fixes flow component")
    assert_matrix_eq(T_big * S_minus, -S_minus, "T negates mirror component")

    J_big = sp.kronecker_product(I3, J)
    mirrored_total = J_big * total * J_big
    expected_mirrored_total = sp.kronecker_product(I3, (sp.Rational(1, 2) + sigma) * I2 - tau * K)
    assert_matrix_eq(mirrored_total, expected_mirrored_total, "mirror acts only on doubled imaginary axis, not on sectors")

    print("combined tensor model: centered coordinate threads through tripotent sectors")


def main() -> None:
    verify_centered_coordinate()
    verify_doubled_polarization()
    verify_trifactor_sectors()
    verify_combined_tensor_model()
    print("CENTERED TRIPOTENT SECTOR GEOMETRY VERIFIED")


if __name__ == "__main__":
    main()
