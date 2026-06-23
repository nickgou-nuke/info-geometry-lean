#!/usr/bin/env python3
"""Finite K3 stabilizer/Hodge witness.

The Lean owner proves the general finite matrix theorem.  This script checks the
concrete K3 incidence matrices:

* the edge-space stabilizer Hamiltonian is the one-form Hodge Laplacian;
* the filled triangle has zero harmonic one-sector;
* the boundary triangle has a harmonic cycle orthogonal to exact errors;
* in the filled triangle, the former boundary cycle is removed by the face
  stabilizer and becomes coexact/Hodge-active.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*simplified.shape):
        raise AssertionError(f"{name} failed:\n{simplified}")
    print(f"ok: {name}")


def incidence_k3() -> tuple[sp.Matrix, sp.Matrix]:
    d0 = sp.Matrix([
        [-1, 1, 0],
        [0, -1, 1],
        [-1, 0, 1],
    ])
    d1 = sp.Matrix([[1, 1, -1]])
    return d0, d1


def hodge_laplacian_1(d0: sp.Matrix, d1: sp.Matrix) -> sp.Matrix:
    return d0 * d0.T + d1.T * d1


def verify_filled_k3_stabilizer() -> None:
    d0, d1 = incidence_k3()
    vertex_check = d0.T
    face_check = d1
    hamiltonian = vertex_check.T * vertex_check + face_check.T * face_check
    laplacian = hodge_laplacian_1(d0, d1)

    assert_zero("filled stabilizer Hamiltonian equals L1", hamiltonian - laplacian)

    if len(laplacian.nullspace()) != 0:
        raise AssertionError("filled K3 clique complex should have ker(L1)=0")
    print("ok: filled K3 code space ker(L1) is zero")

    boundary_cycle = sp.Matrix([1, 1, -1])
    assert_zero("boundary cycle is coclosed", vertex_check * boundary_cycle)
    if face_check * boundary_cycle == sp.zeros(1, 1):
        raise AssertionError("filled face stabilizer should kill the boundary harmonic cycle")
    print("ok: filled face stabilizer removes the boundary harmonic cycle")


def verify_boundary_code_protection() -> None:
    d0, _ = incidence_k3()
    boundary_cycle = sp.Matrix([1, 1, -1])
    l1_boundary = d0 * d0.T
    exact_basis = list(d0.columnspace())

    assert_zero("boundary harmonic cycle L1*c", l1_boundary * boundary_cycle)
    assert_zero("boundary harmonic cycle d0.T*c", d0.T * boundary_cycle)

    for idx, exact in enumerate(exact_basis):
        dot = (boundary_cycle.T * exact)[0]
        if sp.simplify(dot) != 0:
            raise AssertionError(f"harmonic cycle not orthogonal to exact basis {idx}: {dot}")
    print("ok: boundary harmonic cycle is orthogonal to exact error sector")

    if len(l1_boundary.nullspace()) != 1:
        raise AssertionError("boundary K3 graph should have one harmonic code mode")
    print("ok: boundary K3 graph has one harmonic code mode")


def verify_hodge_decomposition_dimensions() -> None:
    d0, d1 = incidence_k3()
    exact_rank = d0.rank()
    coexact_rank = d1.T.rank()
    harmonic_rank = len(hodge_laplacian_1(d0, d1).nullspace())
    edge_dim = d0.shape[0]
    if exact_rank + coexact_rank + harmonic_rank != edge_dim:
        raise AssertionError(
            "filled K3 dimensions do not add: "
            f"{exact_rank}+{coexact_rank}+{harmonic_rank}!={edge_dim}"
        )
    print("ok: filled K3 exact/coexact/harmonic dimensions add to edge space")


def main() -> None:
    print("=== Discrete Hodge Stabilizer K3 Witness ===")
    verify_filled_k3_stabilizer()
    verify_boundary_code_protection()
    verify_hodge_decomposition_dimensions()
    print("=== SUCCESS ===")


if __name__ == "__main__":
    main()
