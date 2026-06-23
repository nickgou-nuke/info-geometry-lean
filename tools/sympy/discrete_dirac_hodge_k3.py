#!/usr/bin/env python3
"""Finite K3/triangle Dirac--Hodge witness.

Lean is the proof authority.  This script checks the concrete incidence-matrix
model used as the finite graph intuition:

* d1 d0 = 0 and d0.T d1.T = 0;
* D = d + d* anticommutes with degree chirality gamma;
* D^2 is the Hodge Laplacian d d* + d* d;
* the filled K3 clique complex has no harmonic 1-cycle, while the boundary
  graph has the expected one-dimensional harmonic cycle.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*simplified.shape):
        raise AssertionError(f"{name} failed:\n{simplified}")
    print(f"ok: {name}")


def incidence_k3() -> tuple[sp.Matrix, sp.Matrix]:
    # Vertices: 0, 1, 2.
    # Oriented edges: e01, e12, e02.
    d0 = sp.Matrix([
        [-1, 1, 0],
        [0, -1, 1],
        [-1, 0, 1],
    ])
    # Filled oriented face (0,1,2): boundary e01 + e12 - e02.
    d1 = sp.Matrix([[1, 1, -1]])
    return d0, d1


def dirac_hodge(d0: sp.Matrix, d1: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix]:
    n0 = d0.shape[1]
    n1 = d0.shape[0]
    n2 = d1.shape[0]
    z00 = sp.zeros(n0, n0)
    z11 = sp.zeros(n1, n1)
    z22 = sp.zeros(n2, n2)
    z01 = sp.zeros(n0, n1)
    z02 = sp.zeros(n0, n2)
    z10 = sp.zeros(n1, n0)
    z12 = sp.zeros(n1, n2)
    z20 = sp.zeros(n2, n0)
    z21 = sp.zeros(n2, n1)

    d_total = sp.Matrix.vstack(
        sp.Matrix.hstack(z00, z01, z02),
        sp.Matrix.hstack(d0, z11, z12),
        sp.Matrix.hstack(z20, d1, z22),
    )
    delta_total = sp.Matrix.vstack(
        sp.Matrix.hstack(z00, d0.T, z02),
        sp.Matrix.hstack(z10, z11, d1.T),
        sp.Matrix.hstack(z20, z21, z22),
    )
    return d_total, delta_total


def hodge_laplacian_expected(d0: sp.Matrix, d1: sp.Matrix) -> sp.Matrix:
    l0 = d0.T * d0
    l1 = d0 * d0.T + d1.T * d1
    l2 = d1 * d1.T
    return sp.diag(l0, l1, l2)


def verify_filled_triangle() -> None:
    d0, d1 = incidence_k3()
    d, delta = dirac_hodge(d0, d1)
    dirac = d + delta
    gamma = sp.diag(1, 1, 1, -1, -1, -1, 1)
    laplacian = hodge_laplacian_expected(d0, d1)

    assert_zero("filled K3 cochain condition d1*d0", d1 * d0)
    assert_zero("filled K3 adjoint condition d0.T*d1.T", d0.T * d1.T)
    assert_zero("d^2 = 0", d * d)
    assert_zero("(d*)^2 = 0", delta * delta)
    assert_zero("{D,gamma} = 0", dirac * gamma + gamma * dirac)
    assert_zero("D^2 = Hodge Laplacian", dirac * dirac - laplacian)

    l1 = d0 * d0.T + d1.T * d1
    if len(l1.nullspace()) != 0:
        raise AssertionError("filled K3 should have b1 = 0")
    print("ok: filled K3 harmonic one-sector is zero")


def verify_boundary_triangle_harmonic_cycle() -> None:
    d0, _ = incidence_k3()
    cycle = sp.Matrix([1, 1, -1])
    assert_zero("boundary K3 coclosed cycle d0.T*c", d0.T * cycle)

    l1_boundary = d0 * d0.T
    nullspace = l1_boundary.nullspace()
    if len(nullspace) != 1:
        raise AssertionError(f"boundary K3 expected b1 = 1, got {len(nullspace)}")
    assert_zero("boundary K3 harmonic cycle L1*c", l1_boundary * cycle)
    print("ok: boundary K3 has one harmonic cycle")


def main() -> None:
    print("=== Discrete Dirac--Hodge K3 Witness ===")
    verify_filled_triangle()
    verify_boundary_triangle_harmonic_cycle()
    print("=== SUCCESS ===")


if __name__ == "__main__":
    main()
