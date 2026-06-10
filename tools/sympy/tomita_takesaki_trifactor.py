#!/usr/bin/env python3
"""Finite algebraic Tomita--Takesaki trifactor checks.

This script is the SymPy companion to
``lean/InfoGeometry/Canonical/TomitaTakesakiTrifactor.lean``.

It checks the finite coordinate-free algebraic shadow:

* modular automorphisms are inner conjugations ``X -> Δ X Δ⁻¹``;
* inner conjugation preserves products, commutators, and curvature;
* the centralizer is the fixed-point algebra of the modular automorphism;
* an involutive Tomita mirror ``J`` flips an odd/phase axis;
* the commutator bracket satisfies Jacobi and acts as a derivation;
* a tripotent operator ``T³ = T`` resolves into ``(+,-,0)`` projectors.

No external certificate is consumed.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    diff = matrix.applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


def commutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def modular_automorphism(delta: sp.Matrix, x: sp.Matrix) -> sp.Matrix:
    return delta * x * delta.inv()


def two_slot_curvature(
    d_xy: sp.Matrix,
    d_yx: sp.Matrix,
    a_x: sp.Matrix,
    a_y: sp.Matrix,
) -> sp.Matrix:
    return d_xy - d_yx + commutator(a_x, a_y)


def symbolic_matrix(prefix: str, n: int) -> sp.Matrix:
    return sp.Matrix(n, n, sp.symbols(f"{prefix}0:{n*n}"))


def verify_modular_automorphism() -> None:
    print("\nmodular automorphism")
    delta = sp.diag(2, 3)
    x = symbolic_matrix("x_", 2)
    y = symbolic_matrix("y_", 2)
    d_xy = symbolic_matrix("dxy_", 2)
    d_yx = symbolic_matrix("dyx_", 2)

    sigma_xy = modular_automorphism(delta, x * y)
    sigma_x_sigma_y = modular_automorphism(delta, x) * modular_automorphism(delta, y)
    assert_matrix_zero("sigma_delta preserves products", sigma_xy - sigma_x_sigma_y)

    sigma_comm = modular_automorphism(delta, commutator(x, y))
    comm_sigma = commutator(modular_automorphism(delta, x), modular_automorphism(delta, y))
    assert_matrix_zero("sigma_delta preserves commutators", sigma_comm - comm_sigma)

    curvature = two_slot_curvature(d_xy, d_yx, x, y)
    sigma_curvature = modular_automorphism(delta, curvature)
    curvature_sigma = two_slot_curvature(
        modular_automorphism(delta, d_xy),
        modular_automorphism(delta, d_yx),
        modular_automorphism(delta, x),
        modular_automorphism(delta, y),
    )
    assert_matrix_zero("sigma_delta preserves curvature", sigma_curvature - curvature_sigma)


def verify_centralizer_fixed_points() -> None:
    print("\ncentralizer fixed points")
    delta = sp.diag(2, 3)
    z0, z1, lam = sp.symbols("z0 z1 lam")
    centralizer_element = sp.diag(z0, z1)
    center_element = lam * sp.eye(2)

    assert_matrix_zero("centralizer commutes with Delta",
                       commutator(delta, centralizer_element))
    assert_matrix_zero("centralizer is fixed by sigma_delta",
                       modular_automorphism(delta, centralizer_element) - centralizer_element)
    assert_matrix_zero("center is fixed by sigma_delta",
                       modular_automorphism(delta, center_element) - center_element)


def verify_tomita_mirror() -> None:
    print("\nTomita mirror")
    j = sp.Matrix([[0, 1], [1, 0]])
    axis = sp.diag(1, -1)
    assert_matrix_zero("J^2 = I", j**2 - sp.eye(2))
    assert_matrix_zero("J axis J = -axis", j * axis * j + axis)
    assert_matrix_zero("J anticommutes with axis", j * axis + axis * j)


def verify_jacobi_and_derivation() -> None:
    print("\nJacobi / derivation")
    x = symbolic_matrix("jx_", 2)
    y = symbolic_matrix("jy_", 2)
    z = symbolic_matrix("jz_", 2)
    h = symbolic_matrix("h_", 2)

    jacobi = (
        commutator(x, commutator(y, z))
        + commutator(y, commutator(z, x))
        + commutator(z, commutator(x, y))
    )
    assert_matrix_zero("commutator Jacobi identity", jacobi)

    derivation = (
        commutator(h, commutator(x, y))
        - commutator(commutator(h, x), y)
        - commutator(x, commutator(h, y))
    )
    assert_matrix_zero("modular derivation preserves bracket", derivation)


def verify_trifactor_projectors() -> None:
    print("\nTomita trifactor projectors")
    t = sp.diag(1, -1, 0)
    p_plus = (t**2 + t) / 2
    p_minus = (t**2 - t) / 2
    p_zero = sp.eye(3) - t**2

    assert_matrix_zero("T^3 = T", t**3 - t)
    assert_matrix_zero("P_plus^2 = P_plus", p_plus**2 - p_plus)
    assert_matrix_zero("P_minus^2 = P_minus", p_minus**2 - p_minus)
    assert_matrix_zero("P_zero^2 = P_zero", p_zero**2 - p_zero)
    assert_matrix_zero("P_plus P_minus = 0", p_plus * p_minus)
    assert_matrix_zero("P_zero P_plus = 0", p_zero * p_plus)
    assert_matrix_zero("P_zero P_minus = 0", p_zero * p_minus)
    assert_matrix_zero("P_plus + P_minus + P_zero = I",
                       p_plus + p_minus + p_zero - sp.eye(3))
    assert_matrix_zero("T = P_plus - P_minus", t - (p_plus - p_minus))


def main() -> int:
    print("=" * 72)
    print("TOMITA-TAKESAKI TRIFACTOR -- FINITE ALGEBRAIC CHECK")
    print("=" * 72)

    verify_modular_automorphism()
    verify_centralizer_fixed_points()
    verify_tomita_mirror()
    verify_jacobi_and_derivation()
    verify_trifactor_projectors()

    print("\nTOMITA-TAKESAKI TRIFACTOR VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
