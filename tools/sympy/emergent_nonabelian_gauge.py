#!/usr/bin/env python3
"""
Finite non-Abelian gauge witness.

Mirrors lean/InfoGeometry/Canonical/EmergentNonAbelianGauge.lean.
This script checks only the finite matrix identities proved there:

* the Pauli generators close cyclically on all three generators;
* the first three Gell-Mann generators close on the corresponding cycle;
* the first generators are nonzero;
* scalar insertion factors out of the spinor bilinear;
* the explicit spinor witnesses give nonzero axial bilinears after insertion.

It does not construct gauge bundles, Yang-Mills curvature, or physical
SU(2)/SU(3) dynamics.
"""

from __future__ import annotations

import sympy as sp
from sympy.physics.matrices import msigma


def pauli_matrices():
    s1, s2, s3 = msigma(1), msigma(2), msigma(3)
    return s1, s2, s3


def gell_mann_matrices():
    lam1 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    lam2 = sp.Matrix([[0, -sp.I, 0], [sp.I, 0, 0], [0, 0, 0]])
    lam3 = sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
    return lam1, lam2, lam3


def dirac_gamma_matrices():
    I2 = sp.eye(2)
    Z2 = sp.zeros(2)
    s1, s2, s3 = pauli_matrices()
    g0 = sp.Matrix(sp.BlockMatrix([[I2, Z2], [Z2, -I2]]))
    g1 = sp.Matrix(sp.BlockMatrix([[Z2, s1], [-s1, Z2]]))
    g2 = sp.Matrix(sp.BlockMatrix([[Z2, s2], [-s2, Z2]]))
    g3 = sp.Matrix(sp.BlockMatrix([[Z2, s3], [-s3, Z2]]))
    g5 = sp.I * g0 * g1 * g2 * g3
    return g0, g1, g2, g3, g5


def matrix_bracket(a, b):
    return a * b - b * a


def dirac_adjoint(psi, g0):
    return (sp.Matrix([sp.conjugate(x) for x in psi]).T) * g0


def spinor_bilinear(psi, m, phi, g0):
    bar = dirac_adjoint(psi, g0)
    return (bar * m * phi)[0]


def gauge_insertion_bilinear(psi, m, ta, g0):
    return spinor_bilinear(psi, m, ta * psi, g0)


def assert_matrix_eq(a, b, label):
    diff = sp.simplify(a - b)
    if diff != sp.zeros(*a.shape):
        raise AssertionError(f"{label} failed:\n{sp.simplify(diff)}")


def assert_scalar_eq(a, b, label):
    diff = sp.simplify(sp.expand(a - b))
    if diff != 0:
        raise AssertionError(f"{label} failed: {diff}")


def main() -> None:
    print("=" * 72)
    print("EMERGENT NON-ABELIAN GAUGE -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    tau1, tau2, tau3 = pauli_matrices()
    lam1, lam2, lam3 = gell_mann_matrices()
    g0, g1, g2, g3, g5 = dirac_gamma_matrices()

    assert_matrix_eq(matrix_bracket(tau1, tau2), 2 * sp.I * tau3, "[tau1, tau2] = 2i tau3")
    assert_matrix_eq(matrix_bracket(tau2, tau3), 2 * sp.I * tau1, "[tau2, tau3] = 2i tau1")
    assert_matrix_eq(matrix_bracket(tau3, tau1), 2 * sp.I * tau2, "[tau3, tau1] = 2i tau2")
    assert_matrix_eq(matrix_bracket(lam1, lam2), 2 * sp.I * lam3, "[lambda1, lambda2] = 2i lambda3")
    assert_matrix_eq(matrix_bracket(lam2, lam3), 2 * sp.I * lam1, "[lambda2, lambda3] = 2i lambda1")
    assert_matrix_eq(matrix_bracket(lam3, lam1), 2 * sp.I * lam2, "[lambda3, lambda1] = 2i lambda2")
    print("  Pauli and first Gell-Mann commutators verified")

    if tau1 == sp.zeros(2) or lam1 == sp.zeros(3):
        raise AssertionError("first generators unexpectedly vanished")
    print("  first generators are nonzero")

    p0, p1, p2, p3 = sp.symbols("p0 p1 p2 p3", complex=True)
    q0, q1, q2, q3 = sp.symbols("q0 q1 q2 q3", complex=True)
    ta = sp.symbols("ta", complex=True)
    psi = sp.Matrix([p0, p1, p2, p3])
    phi = sp.Matrix([q0, q1, q2, q3])

    g0g5 = g5 * g0
    lhs = gauge_insertion_bilinear(psi, g0g5, ta, g0)
    rhs = ta * spinor_bilinear(psi, g0g5, psi, g0)
    assert_scalar_eq(lhs, rhs, "scalar insertion factors out")
    print("  scalar insertion factorization verified")

    spinor_temporal = sp.Matrix([1, 0, 1, 0])
    spinor_spatial = sp.Matrix([1, 1, 0, 0])
    temporal_value = sp.simplify(gauge_insertion_bilinear(spinor_temporal, g0g5, 1, g0))
    spatial_value = sp.simplify(
        gauge_insertion_bilinear(spinor_spatial, g5 * g1, 1, g0)
    )
    if temporal_value == 0 or spatial_value == 0:
        raise AssertionError(
            f"expected nonzero witnesses, got temporal={temporal_value}, spatial={spatial_value}"
        )
    print(f"  temporal witness = {temporal_value}")
    print(f"  spatial witness = {spatial_value}")

    print("=" * 72)
    print("EMERGENT NON-ABELIAN GAUGE VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
