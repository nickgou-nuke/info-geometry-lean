#!/usr/bin/env python3
"""Finite witness for the constructive Bost-Connes superalgebra interface.

This mirrors `InfoGeometry.Canonical.BostConnesSuperalgebraConstructive`.

It verifies only finite algebraic shadows:
1. the local bosonic Euler factor is inverted by the local Witten factor;
2. a two-state CAR generator is parity-odd;
3. parity-invariant trace readout vanishes on parity-odd elements.

No infinite UHF algebra, KMS phase transition, BEC theorem, or RH consequence is
claimed here.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== CONSTRUCTIVE BOST-CONNES SUPERALGEBRA WITNESS ===")

    x = sp.symbols("x")
    bosonic_factor = 1 / (1 - x)
    witten_factor = 1 - x
    euler_inverse_gap = sp.simplify(bosonic_factor * witten_factor - 1)
    print(f"[1] Z_B(x) * W(x) - 1 = {euler_inverse_gap}")
    assert euler_inverse_gap == 0

    a = sp.Matrix([[0, 1], [0, 0]])
    astar = a.T
    gamma = sp.diag(1, -1)

    car_nilpotent = a * a
    car_relation = a * astar + astar * a
    parity_action = gamma * a * gamma

    print(f"[2] a^2 = {car_nilpotent}")
    print(f"[3] a a* + a* a = {car_relation}")
    print(f"[4] Gamma a Gamma = {parity_action}")
    assert car_nilpotent == sp.zeros(2)
    assert car_relation == sp.eye(2)
    assert parity_action == -a

    odd = sp.Matrix([[0, sp.symbols("b")], [sp.symbols("c"), 0]])
    odd_parity_gap = sp.simplify(gamma * odd * gamma + odd)
    invariant_trace_gap = sp.simplify(sp.trace(odd))

    print(f"[5] Gamma O Gamma + O = {odd_parity_gap}")
    print(f"[6] trace(O) for parity-odd O = {invariant_trace_gap}")
    assert odd_parity_gap == sp.zeros(2)
    assert invariant_trace_gap == 0

    print("=== SUCCESS: FINITE PARITY SUPERCANCELLATION VERIFIED ===")


if __name__ == "__main__":
    main()

