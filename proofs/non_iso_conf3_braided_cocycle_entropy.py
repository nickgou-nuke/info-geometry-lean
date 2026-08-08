#!/usr/bin/env python3
"""SymPy witness for Conf3 edge cocycles, Wilson loops, and broken balance.

For positive edge ratios r_ij, set a_ij = log(r_ij).  The triangle cycle defect

    Δ = a12 + a23 - a13

is the additive Wilson/entropy cocycle.  Exponentiating gives

    exp(Δ) = r12*r23/r13.

Detailed balance is Δ=0, equivalently r13 = r12*r23.  Broken detailed balance
is a nontrivial Wilson loop.
"""

from __future__ import annotations

import sympy as sp


r12, r23, r13 = sp.symbols("r12 r23 r13", positive=True)

a12 = sp.log(r12)
a23 = sp.log(r23)
a13 = sp.log(r13)

cycle_defect = sp.simplify(a12 + a23 - a13)
wilson_loop = sp.simplify(sp.exp(cycle_defect))


def main() -> None:
    expected_loop = r12 * r23 / r13
    assert sp.simplify(wilson_loop - expected_loop) == 0

    balanced_defect = sp.simplify(cycle_defect.subs(r13, r12 * r23))
    assert balanced_defect == 0

    reversed_defect = sp.simplify((-a23) + (-a12) - (-a13))
    assert sp.simplify(reversed_defect + cycle_defect) == 0
    assert sp.simplify(sp.exp(reversed_defect) - 1 / wilson_loop) == 0

    numeric_broken = cycle_defect.subs({r12: 2, r23: 3, r13: 5})
    assert sp.simplify(numeric_broken - sp.log(sp.Rational(6, 5))) == 0

    print("cycle defect Δ =", cycle_defect)
    print("Wilson loop exp(Δ) =", wilson_loop)
    print("balanced condition: r13 = r12*r23 -> Δ = 0")
    print("braid/orientation reversal: Δ -> -Δ, Wilson -> Wilson^{-1}")
    print("broken detailed balance sample: r12=2,r23=3,r13=5 -> Δ =", numeric_broken)
    print("non_iso_conf3_braided_cocycle_entropy.py: cocycle/Wilson audit passed")


if __name__ == "__main__":
    main()

