#!/usr/bin/env python3
"""
Two-sheet complex polarization verification.

This mirrors lean/InfoGeometry/Canonical/TwoSheetComplexPolarization.lean with
finite real matrices.  It checks that the square-minus-one complex axis emerges
from two real involutions rather than from a primitive complex scalar.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def bregman_free_energy(x: sp.Expr) -> sp.Expr:
    return sp.exp(x) - 1 - x


def main() -> None:
    print("=" * 72)
    print("TWO-SHEET COMPLEX POLARIZATION -- SYMPY VERIFICATION")
    print("=" * 72)

    identity = sp.eye(2)
    epsilon = sp.Matrix([[1, 0], [0, -1]])
    sheet_swap = sp.Matrix([[0, 1], [1, 0]])
    emergent_k = sheet_swap * epsilon

    assert_matrix_eq(sheet_swap * sheet_swap, identity, "J^2 = I")
    assert_matrix_eq(epsilon * epsilon, identity, "epsilon^2 = I")
    assert_matrix_eq(sheet_swap * epsilon, -(epsilon * sheet_swap), "J epsilon = - epsilon J")
    assert_matrix_eq(emergent_k, sp.Matrix([[0, -1], [1, 0]]), "K = J epsilon")
    assert_matrix_eq(emergent_k * emergent_k, -identity, "K^2 = -I")
    assert_matrix_eq(sheet_swap * emergent_k * sheet_swap, -emergent_k, "J K J = -K")
    print("  real involutions generate K^2 = -I")

    physical_projector = sp.Rational(1, 2) * (identity + epsilon)
    ghost_projector = sp.Rational(1, 2) * (identity - epsilon)
    assert_matrix_eq(physical_projector, sp.Matrix([[1, 0], [0, 0]]), "physical projector")
    assert_matrix_eq(ghost_projector, sp.Matrix([[0, 0], [0, 1]]), "ghost projector")
    assert_matrix_eq(physical_projector * physical_projector, physical_projector, "P+ idempotent")
    assert_matrix_eq(ghost_projector * ghost_projector, ghost_projector, "P- idempotent")
    assert_matrix_eq(physical_projector + ghost_projector, identity, "P+ + P- = I")
    print("  two sheet projectors verified")

    shift_l = sp.Matrix([[0, 1], [0, 0]])
    shift_r = sp.Matrix([[0, 0], [1, 0]])
    dirac_hodge = shift_l + sheet_swap * shift_l * sheet_swap
    assert_matrix_eq(sheet_swap * shift_l * sheet_swap, shift_r, "J S_L J = S_R")
    assert_matrix_eq(dirac_hodge, shift_l + shift_r, "D = S_L + J S_L J")
    assert_matrix_eq(dirac_hodge, sheet_swap, "finite Dirac-Hodge hop is sheet swap")
    print("  finite Dirac-Hodge hopping operator verified")

    if sp.simplify(bregman_free_energy(0)) != 0:
        raise AssertionError("Bregman free energy should vanish at zero")
    print("  Bregman free-energy zero point verified")

    print("=" * 72)
    print("TWO-SHEET POLARIZATION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()

