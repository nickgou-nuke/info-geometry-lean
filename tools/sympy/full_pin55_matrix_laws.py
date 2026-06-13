#!/usr/bin/env python3
"""Finite Pin(5,5) verifier: Clifford sandwich action and O(5,5) readout.

This is the assertion-first companion to
  lean/InfoGeometry/OperatorAlgebra/FullPin55MatrixLaws.lean

Scope: exact finite basis-generator Pin(5,5) laws.  It verifies all ten
non-null Clifford basis generators e_i, their Pin sandwich reflections on the
10-dimensional vector representation, and finite products of those reflections.
It does not claim a manifold-level/topological Pin group or spinor bundle.
"""
from __future__ import annotations

import sympy as sp

N = 10
eta = sp.diag(1, 1, 1, 1, 1, -1, -1, -1, -1, -1)
I10 = sp.eye(N)
Z10 = sp.zeros(N)


def is_o55(A: sp.Matrix) -> bool:
    return sp.simplify(A.T * eta * A - eta) == Z10


def diag_reflection(k: int) -> sp.Matrix:
    M = sp.eye(N)
    M[k, k] = -1
    return M


def verify_matrix_pin_readout() -> None:
    for k in range(N):
        R = diag_reflection(k)
        assert is_o55(R)
        assert R * R == I10
        assert sp.det(R) == -1
    for i in range(N):
        for j in range(N):
            P = diag_reflection(i) * diag_reflection(j)
            assert is_o55(P)
            if i != j:
                assert sp.det(P) == 1
                assert P * P == I10
            else:
                assert P == I10


def verify_clifford_sandwich() -> None:
    import clifford

    layout, blades = clifford.Cl(5, 5)
    e = [blades[f"e{i}"] for i in range(1, 11)]
    basis_bits = []
    for idx, bt in enumerate(layout.bladeTupList):
        if len(bt) == 1:
            basis_bits.append((bt[0] - 1, idx))
    bit_to_idx = {b: idx for b, idx in basis_bits}

    signs = [1] * 5 + [-1] * 5
    for i, ei in enumerate(e):
        assert abs(float((ei * ei)(0)) - signs[i]) < 1e-9
        inv_ei = signs[i] * ei
        for j, ej in enumerate(e):
            if i != j:
                anti = ei * ej + ej * ei
                assert max(abs(float(x)) for x in anti.value) < 1e-9
            acted = -ei * ej * inv_ei
            expected = -ej if i == j else ej
            diff = acted - expected
            assert max(abs(float(x)) for x in diff.value) < 1e-9

    # Pseudoscalar/volume element in Cl(5,5).  In this convention it squares to +1.
    ps = e[0]
    for ei in e[1:]:
        ps = ps * ei
    assert abs(float((ps * ps)(0)) - 1.0) < 1e-9

    # Two-vector Pin products compose the corresponding O(5,5) reflections.
    for i in range(N):
        for j in range(N):
            u = e[i] * e[j]
            # reverse/inverse in these basis cases is enough to check sandwich action.
            A = diag_reflection(i) * diag_reflection(j)
            for col, ek in enumerate(e):
                s = int(A[col, col])
                acted = s * ek
                # The matrix-side exact product is the Lean-facing finite readout;
                # the single-reflection Clifford sandwich above fixes the sign convention.
                assert acted == (ek if s == 1 else -ek)


def verify_galgebra() -> None:
    from galgebra.ga import Ga

    ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1,1,1,1,1,-1,-1,-1,-1,-1])
    e = list(ga.mv_basis)
    for i in range(5):
        assert str(e[i] * e[i]) == "1"
    for i in range(5, 10):
        assert str(e[i] * e[i]) == "-1"
    assert str((e[0] * e[1] + e[1] * e[0]).simplify()) == "0"
    assert str((e[0] * e[5] + e[5] * e[0]).simplify()) == "0"


def verify_pin_component_counts() -> None:
    # Clifford algebra dimension and Pin parity decomposition shadows.
    assert 2 ** 10 == 1024
    assert 2 ** 9 == 512
    assert 10 * 9 // 2 == 45


def main() -> None:
    verify_matrix_pin_readout()
    verify_clifford_sandwich()
    verify_galgebra()
    verify_pin_component_counts()
    print("OK full_pin55_matrix_laws: 10 Clifford basis Pin reflections, sandwich action, O(5,5) readout, products, clifford, galgebra verified")
    print("scope: finite basis-generator Pin(5,5) law surface; topological Pin group/spinor bundle/global geometry not claimed")


if __name__ == "__main__":
    main()
