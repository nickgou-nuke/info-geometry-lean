#!/usr/bin/env python3
"""SymPy witness for the Tomita creation/annihilation bridge.

This mirrors `InfoGeometry.Canonical.CreationAnnihilationTomitaBridge`.

The script verifies the finite split-Cl(1,1) / one-mode CAR shadow:

* creation and annihilation are nilpotent;
* their anticommutator is the identity;
* the Tomita mirror swaps creation and annihilation;
* creation + annihilation is J-even;
* creation - annihilation is J-odd.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_eq(lhs: sp.Matrix, rhs: sp.Matrix, label: str) -> None:
    delta = sp.simplify(lhs - rhs)
    if delta != sp.zeros(*lhs.shape):
        raise AssertionError(f"{label} failed:\n{delta}")


def main() -> None:
    identity = sp.eye(2)
    zero = sp.zeros(2)

    # One-mode CAR matrices on basis |0>, |1>.
    annihilation = sp.Matrix([[0, 1], [0, 0]])
    creation = sp.Matrix([[0, 0], [1, 0]])

    # Tomita mirror: swaps the two null directions.
    J = sp.Matrix([[0, 1], [1, 0]])

    assert_matrix_eq(annihilation**2, zero, "annihilation nilpotent")
    assert_matrix_eq(creation**2, zero, "creation nilpotent")
    assert_matrix_eq(annihilation * creation + creation * annihilation, identity, "CAR")

    assert_matrix_eq(J**2, identity, "J involution")
    assert_matrix_eq(J * creation * J, annihilation, "J creation J = annihilation")
    assert_matrix_eq(J * annihilation * J, creation, "J annihilation J = creation")

    even_majorana = creation + annihilation
    odd_density = creation - annihilation
    assert_matrix_eq(J * even_majorana * J, even_majorana, "even Majorana fixed")
    assert_matrix_eq(J * odd_density * J, -odd_density, "odd density anti-fixed")

    vacuum_projector = annihilation * creation
    number_projector = creation * annihilation
    assert_matrix_eq(vacuum_projector**2, vacuum_projector, "vacuum projector")
    assert_matrix_eq(number_projector**2, number_projector, "number projector")
    assert_matrix_eq(vacuum_projector + number_projector, identity, "projector partition")

    print("creation_annihilation_tomita_bridge: ok")
    print("  nilpotent: a^2 = 0 and c^2 = 0")
    print("  CAR: a*c + c*a = I")
    print("  Tomita mirror: J*c*J = a and J*a*J = c")
    print("  even sector: J*(c+a)*J = c+a")
    print("  odd sector: J*(c-a)*J = -(c-a)")


if __name__ == "__main__":
    main()
