#!/usr/bin/env python3
"""Finite repaired Section 28 tensor-algebra witness.

Mirrors `InfoGeometry.Physics.Section28EinsteinTorsionSpinor`.

Checks only finite 4x4 algebraic identities:
- symmetrized spinor-stress shadow is symmetric if the metric is symmetric;
- torsion-square and curvature-square algebraic stress shadows are symmetric
  under symmetric inputs;
- a constructed modified Einstein residual vanishes exactly when the component
  equation is satisfied.

No continuum variation, Bach tensor identity, Bianchi identity, Dirac equation,
or Einstein--Cartan field theorem is asserted.
"""

import sympy as sp


def symmetric_matrix(prefix: str) -> sp.Matrix:
    entries = {}
    M = sp.zeros(4)
    for i in range(4):
        for j in range(i, 4):
            x = sp.symbols(f"{prefix}{i}{j}")
            M[i, j] = x
            M[j, i] = x
            entries[(i, j)] = x
    return M


def raw_matrix(prefix: str) -> sp.Matrix:
    return sp.Matrix(4, 4, lambda i, j: sp.symbols(f"{prefix}{i}{j}"))


def is_symmetric(M: sp.Matrix) -> bool:
    return sp.simplify(M - M.T) == sp.zeros(4)


def main() -> None:
    g = symmetric_matrix("g")
    G = symmetric_matrix("G")
    H = symmetric_matrix("H")
    A = raw_matrix("A")
    B = symmetric_matrix("B")

    trA, torsion_norm = sp.symbols("trA tau")
    Lambda, alpha1, alpha2, eightPiG = sp.symbols("Lambda alpha1 alpha2 eightPiG")

    spinor_stress = sp.Rational(1, 4) * (A + A.T) - sp.Rational(1, 4) * trA * g
    torsion_stress = 2 * alpha2 * (B - sp.Rational(1, 4) * torsion_norm * g)
    curvature_stress = alpha1 * (2 * H - sp.Rational(1, 2) * sp.symbols("rho") * g)

    lhs = G + Lambda * g + alpha1 * H
    rhs = eightPiG * (spinor_stress + torsion_stress)
    residual = sp.simplify(lhs - rhs)

    # Construct an on-shell Einstein tensor so that the residual vanishes.
    G_on_shell = sp.simplify(rhs - Lambda * g - alpha1 * H)
    residual_on_shell = sp.simplify(G_on_shell + Lambda * g + alpha1 * H - rhs)

    print("=== Repaired Section 28 finite tensor algebra ===")
    print(f"spinor stress symmetric: {is_symmetric(spinor_stress)}")
    print(f"torsion stress symmetric: {is_symmetric(torsion_stress)}")
    print(f"curvature-square algebraic stress symmetric: {is_symmetric(curvature_stress)}")
    print(f"residual symmetric under symmetric supplied terms: {is_symmetric(residual)}")
    print(f"on-shell residual is zero matrix: {residual_on_shell == sp.zeros(4)}")

    if (
        is_symmetric(spinor_stress)
        and is_symmetric(torsion_stress)
        and is_symmetric(curvature_stress)
        and is_symmetric(residual)
        and residual_on_shell == sp.zeros(4)
    ):
        print("[SUCCESS] repaired finite Section 28 tensor identities verified.")


if __name__ == "__main__":
    main()
