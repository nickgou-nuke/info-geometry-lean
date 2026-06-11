#!/usr/bin/env python3
"""Finite Virasoro/Drazin/Witten synthesis witness.

This mirrors
`lean/InfoGeometry/GrandUnification/VirasoroDrazinWittenUnification.lean`.

It verifies only finite algebra:

* two nilpotent SUSY charges satisfy `(Q + R)^2 = Q R + R Q`;
* a tripotent operator `O` is its own Drazin inverse and has
  `P_D = O^2 = P_plus + P_minus`, `P_null = P_zero`;
* a supplied central-charge readout with zero null contribution is supported on
  the active Drazin sector;
* paired nonzero boson/fermion levels cancel in a finite Witten supertrace;
* the realified Pauli pseudoscalar squares to `-I`.

No infinite colimit, Virasoro representation, Sugawara construction, continuum
STA/Maxwell equation, or zeta/RH statement is asserted here.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_eq(left: sp.Matrix, right: sp.Matrix, label: str) -> None:
    diff = sp.simplify(left - right)
    if diff != sp.zeros(*left.shape):
        raise AssertionError(f"{label} failed:\n{diff}")


def finite_susy_square() -> None:
    q = sp.Matrix([[0, 1], [0, 0]])
    r = sp.Matrix([[0, 0], [1, 0]])
    h_plus_z = q * r + r * q

    assert_matrix_eq(q * q, sp.zeros(2), "Q^2 = 0")
    assert_matrix_eq(r * r, sp.zeros(2), "R^2 = 0")
    assert_matrix_eq((q + r) * (q + r), h_plus_z, "(Q + R)^2 = {Q,R}")
    print("finite SUSY Dirac-square closure verified")


def drazin_tripotent_split() -> None:
    one = sp.Integer(1)
    O = sp.diag(1, -1, 0)
    OD = O
    P_plus = sp.diag(1, 0, 0)
    P_minus = sp.diag(0, 1, 0)
    P_zero = sp.diag(0, 0, 1)
    PD = O * OD
    P_null = sp.eye(3) - PD

    assert_matrix_eq(O**3, O, "O^3 = O")
    assert_matrix_eq(O**2 * OD, O, "Drazin index-1 law O^2 O^D = O")
    assert_matrix_eq(OD * O * OD, OD, "Drazin solvability O^D O O^D = O^D")
    assert_matrix_eq(O * OD, OD * O, "Drazin commutativity")
    assert_matrix_eq(PD, O**2, "P_D = O^2")
    assert_matrix_eq(PD, P_plus + P_minus, "P_D = P_plus + P_minus")
    assert_matrix_eq(P_null, P_zero, "P_null = P_zero")
    assert_matrix_eq(O * P_null, sp.zeros(3), "O P_null = 0")

    virasoro_central_charge = one
    active_central_charge = one
    null_central_charge = sp.Integer(0)
    assert sp.simplify(
        virasoro_central_charge - (active_central_charge + null_central_charge)
    ) == 0
    assert sp.simplify(virasoro_central_charge - active_central_charge) == 0
    print("Drazin active/null central-charge readout verified")


def finite_witten_cancellation() -> None:
    # zero level contributes +1; two nonzero levels are boson/fermion paired.
    levels = [0, 1, 2]
    zero_levels = {0}
    boson = {0: 1, 1: 2, 2: 3}
    fermion = {0: 0, 1: 2, 2: 3}
    weight = {0: 1, 1: sp.symbols("w1"), 2: sp.symbols("w2")}

    finite_supertrace = sum(
        (boson[i] - fermion[i]) * weight[i] for i in levels
    )
    finite_witten_index = sum(
        boson[i] - fermion[i] for i in levels if i in zero_levels
    )
    assert sp.simplify(finite_supertrace - finite_witten_index) == 0
    print("finite Witten supertrace collapse verified")


def real_pseudoscalar_phase() -> None:
    I4 = sp.eye(4)
    real_phase = sp.Matrix(
        [[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]]
    )
    real_sigma1 = sp.Matrix(
        [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]
    )
    real_sigma2 = sp.Matrix(
        [[0, 0, 0, 1], [0, 0, -1, 0], [0, -1, 0, 0], [1, 0, 0, 0]]
    )
    real_sigma3 = sp.diag(1, 1, -1, -1)

    pseudoscalar = real_sigma1 * real_sigma2 * real_sigma3
    assert_matrix_eq(pseudoscalar, real_phase, "real pseudoscalar = phase axis")
    assert_matrix_eq(real_phase * real_phase, -I4, "real phase axis squared = -I")
    print("real Gull-Doran pseudoscalar phase verified")


def main() -> None:
    finite_susy_square()
    drazin_tripotent_split()
    finite_witten_cancellation()
    real_pseudoscalar_phase()
    print("finite Virasoro/Drazin/Witten synthesis witness: PASS")


if __name__ == "__main__":
    main()

