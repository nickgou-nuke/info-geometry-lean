#!/usr/bin/env python3
"""Finite Drazin/tripotent/trifactor witness.

Mirrors `InfoGeometry.Canonical.DrazinTripotentTrifactorBridge`.

The checked statement is purely finite algebra:

    T^3 = T  ==>  T^D = T,
    P_D = T T^D = T^2 = P_plus + P_minus,
    1 - P_D = P_zero.

It does not assert KMS, critical-line localization, Riemann-zero confinement,
or an infinite-dimensional Witten-index theorem.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main():
    # Concrete tripotent normal form with +1, -1, and 0 sectors.
    T = sp.diag(1, -1, 0)
    I = sp.eye(3)

    TD = T
    PD = T * TD
    P_zero = I - T**2
    P_plus = (T**2 + T) / 2
    P_minus = (T**2 - T) / 2
    P_null = I - PD

    assert_matrix_eq(T**3, T, "tripotent law T^3 = T")

    # Drazin inverse, index 1, in the convention used by the Lean owner.
    assert_matrix_eq(TD * T * TD, TD, "D T D = D")
    assert_matrix_eq(T * TD, TD * T, "T D = D T")
    assert_matrix_eq(T, T**2 * TD, "T^1 = T^2 D")

    assert_matrix_eq(PD, T**2, "Drazin support P_D = T^2")
    assert_matrix_eq(PD**2, PD, "Drazin support idempotent")
    assert_matrix_eq(PD, P_plus + P_minus, "P_D = P_plus + P_minus")
    assert_matrix_eq(P_null, P_zero, "1 - P_D = P_zero")
    assert_matrix_eq(T * P_null, sp.zeros(3), "T annihilates Drazin null sector")

    print("\nDrazin/trifactor finite readout:")
    print(f"T =\n{T}")
    print(f"P_D = T^2 =\n{PD}")
    print(f"P_zero = 1 - P_D =\n{P_zero}")


if __name__ == "__main__":
    main()
