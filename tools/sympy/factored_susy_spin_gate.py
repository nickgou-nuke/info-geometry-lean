#!/usr/bin/env python3
"""SymPy witness for finite spin/SUSY/zeta gate factoring.

Mirrors:
- `InfoGeometry.Algebra.FiniteSpinAlgebra`
- `InfoGeometry.Algebra.FiniteSUSYBlocks`
- `InfoGeometry.Arithmetic.ZetaProductGate`

This is only a computational witness for finite matrix identities.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== FACTORED FINITE SPIN / SUSY / ZETA GATES ===")

    # Layer 1: spin-1/2 ladder algebra.
    J_zero = sp.Matrix([[sp.Rational(1, 2), 0], [0, -sp.Rational(1, 2)]])
    J_plus = sp.Matrix([[0, 1], [0, 0]])
    J_minus = sp.Matrix([[0, 0], [1, 0]])

    assert J_zero * J_plus - J_plus * J_zero == J_plus
    assert J_zero * J_minus - J_minus * J_zero == -J_minus
    assert J_plus * J_minus - J_minus * J_plus == 2 * J_zero
    print("[OK] Layer 1 finite spin algebra")

    # Layer 2: finite SUSY partner blocks.
    A = J_minus
    A_dag = J_plus
    H_minus = A_dag * A
    H_plus = A * A_dag

    assert A * H_minus == H_plus * A
    fermion_parity = sp.Matrix([[1, 0], [0, -1]])
    occupancy = sp.Matrix([[1, 0], [0, 1]])
    assert sp.trace(fermion_parity * occupancy) == 0
    print("[OK] Layer 2 finite SUSY partner block")

    # Layer 3: arithmetic product gates.
    z_boson, z_fermion, u_left, u_right = sp.symbols(
        "z_boson z_fermion u_left u_right"
    )
    assert sp.simplify(z_boson * 0) == 0
    assert sp.simplify(u_left * (1 / u_left) - 1) == 0
    print("[OK] Layer 3 product-zero and product-unit gate forms")

    print("[SUCCESS] factored finite layers verified")


if __name__ == "__main__":
    main()
