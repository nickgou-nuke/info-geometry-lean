#!/usr/bin/env python3
"""Finite witness for the centered-zeta symmetry heuristic boundary.

This script mirrors the Lean module
`InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement`.

It verifies:
1. `s = 1/2 + z` turns `s -> 1 - s` into `z -> -z`;
2. evenness reflects zeros but does not force `Re(z) = 0`;
3. the finite Cartan-complement model kills active components only when the
   invariance/complement hypothesis is supplied.

It deliberately does not assert that Riemann zeta zeros satisfy that complement.
"""

import sympy as sp


def main() -> None:
    u, v = sp.symbols("u v", real=True)
    z = u + sp.I * v
    s = sp.Rational(1, 2) + z
    reflected_s = 1 - s
    centered_reflection = sp.Rational(1, 2) - z

    print("=== CENTERED SYMMETRY HEURISTIC COMPLEMENT ===")

    reflection_gap = sp.simplify(reflected_s - centered_reflection)
    print(f"[1] (1 - (1/2 + z)) - (1/2 - z) = {reflection_gap}")
    assert reflection_gap == 0

    x = sp.symbols("x")
    even_witness = x**2 - 1
    even_gap = sp.expand(even_witness.subs(x, -x) - even_witness)
    zero_at_one = sp.simplify(even_witness.subs(x, 1))
    zero_at_neg_one = sp.simplify(even_witness.subs(x, -1))

    print(f"[2] even witness f(x)=x^2-1, f(-x)-f(x) = {even_gap}")
    print(f"[3] f(1) = {zero_at_one}, f(-1) = {zero_at_neg_one}, Re(1) != 0")
    assert even_gap == 0
    assert zero_at_one == 0
    assert zero_at_neg_one == 0

    a, b, c = sp.symbols("a b c")
    rho = sp.Matrix([a, b, c])
    theta = sp.diag(-1, -1, 1)
    invariance_gap = sp.simplify(theta * rho - rho)
    active_solution = sp.solve(list(invariance_gap), [a, b], dict=True)

    print(f"[4] Theta*rho - rho = {list(invariance_gap)}")
    print(f"[5] finite complement solution for active coordinates = {active_solution}")
    assert active_solution == [{a: 0, b: 0}]

    print("=== SUCCESS: SYMMETRY PAIRS ZEROS; COMPLEMENT IS A SEPARATE HYPOTHESIS ===")


if __name__ == "__main__":
    main()

