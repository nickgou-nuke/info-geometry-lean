#!/usr/bin/env python3
"""Finite O(5,5) light-cone projection and zero-intercept mass readout.

Mirrors `InfoGeometry.Canonical.O55LightConeSpectrumBridge`.

The script verifies only finite algebra:

* the proposed 10x10 change-of-basis matrix is orthogonal;
* the first doubled cell is converted to light-cone coordinates;
* the zero-intercept mass formula gives a massless ground-state readout and
  first-excited readout `4 / alpha_prime`.

No BRST, Virasoro, modular-invariance, E6(6), or physical string-spectrum
claim is asserted here.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_eq(left: sp.Matrix, right: sp.Matrix, label: str) -> None:
    diff = sp.simplify(left - right)
    if diff != sp.zeros(*left.shape):
        raise AssertionError(f"{label} failed:\n{diff}")


def main() -> None:
    sqrt2 = sp.sqrt(2)
    c = 1 / sqrt2
    alpha_prime = sp.symbols("alpha_prime", nonzero=True)

    m = sp.eye(10)
    m[0, 0] = c
    m[0, 1] = c
    m[1, 0] = c
    m[1, 1] = -c

    assert_matrix_eq(m.T * m, sp.eye(10), "M^T M = I")
    assert sp.simplify(2 * c * c) == 1

    doubled = sp.Matrix(sp.symbols("Xp1 Xm1 Xp2 Xm2 Xp3 Xm3 Xp4 Xm4 Xp5 Xm5"))
    string_basis = sp.simplify(m * doubled)

    expected_light_cone = sp.Matrix([
        (doubled[0] + doubled[1]) / sqrt2,
        (doubled[0] - doubled[1]) / sqrt2,
        *list(doubled[2:]),
    ])
    assert_matrix_eq(string_basis, expected_light_cone, "light-cone coordinate readout")

    def standard_mass_sq(level: int, intercept: int) -> sp.Expr:
        return sp.simplify((4 / alpha_prime) * (level - intercept))

    def doubled_mass_sq(level: int) -> sp.Expr:
        return sp.simplify((4 / alpha_prime) * level)

    assert standard_mass_sq(0, 0) == doubled_mass_sq(0) == 0
    assert doubled_mass_sq(1) == 4 / alpha_prime
    assert doubled_mass_sq(2) == 8 / alpha_prime

    print("o55_light_cone_spectrum_bridge: PASS")
    print("  M^T M = I for c = 1/sqrt(2)")
    print("  first doubled cell maps to X^+, X^-")
    print("  zero-intercept mass readout: N=0 -> 0, N=1 -> 4/alpha_prime")


if __name__ == "__main__":
    main()

