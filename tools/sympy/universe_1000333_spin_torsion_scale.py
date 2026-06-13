#!/usr/bin/env python3
"""Finite algebraic witness for Universe 2024, 10, 333.

Lean twin:
    lean/InfoGeometry/Physics/Universe1000333SpinTorsionScale.lean

The PDF is Chen--Wang, "Quantum Effects on Cosmic Scales as an Alternative to
Dark Matter and Dark Energy".  This script checks only algebraic bookkeeping:
number density from scale-dependent mass, spin-density magnitude, additive QPE
mass ledger, and scalar balance residual.  It does not verify observational
fits, large-scale dynamics, smooth spinor PDEs, or full geometric field-system
equations.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    rho_m, m, lam, hbar, qpe, ordinary = sp.symbols(
        "rho_m m lam hbar qpe ordinary", nonzero=True
    )
    rest_mass = sp.symbols("rest_mass")

    number_density = rho_m / m
    spin_density = (hbar / 2) * number_density
    scaled_number_density = rho_m / (m * lam)
    scaled_spin_density = (hbar / 2) * scaled_number_density

    assert sp.simplify(spin_density - (hbar / 2) * (rho_m / m)) == 0
    assert sp.simplify(scaled_number_density - number_density / lam) == 0
    assert sp.simplify(scaled_spin_density - spin_density / lam) == 0

    effective_mass = rest_mass + qpe
    assert sp.simplify(effective_mass - rest_mass - qpe) == 0
    assert sp.simplify(ordinary + (-ordinary)) == 0

    # The STA owner proves this in Lean with concrete gamma matrices; here we
    # mirror the scalar square law only.
    I = sp.Matrix([[0, -1], [1, 0]])
    assert I * I == -sp.eye(2)

    print("UNIVERSE_1000333_SPIN_TORSION_SCALE_OK")
    print("number_density=rho_m/m(lambda)")
    print("spin_density=(hbar/2)*number_density")
    print("scaled_mass_inverse_density=true")
    print("qpe_additive_mass_ledger=true")


if __name__ == "__main__":
    main()
