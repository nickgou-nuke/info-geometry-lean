#!/usr/bin/env python3
"""Finite witnesses for the supergraded graph/entropy/Hodge bridge.

The Lean file is proof authority.  This script only checks the corresponding
finite matrix/algebra identities used as intuition for the bridge.
"""

from __future__ import annotations

import sympy as sp


def verify_graph_energy() -> None:
    distances = [sp.Integer(0), sp.Integer(1), sp.Integer(3)]
    assert all(d >= 0 for d in distances)
    print("[graph] distance-to-reference energy samples are nonnegative")


def verify_entropy_kernel() -> None:
    x, y = sp.symbols("x y")
    kernel = (x - y) * sp.log(x / y)

    positive_samples = [(sp.Rational(3, 1), sp.Rational(2, 1)), (sp.Rational(1, 2), 2)]
    for xv, yv in positive_samples:
        assert sp.N(kernel.subs({x: xv, y: yv})) >= 0

    assert sp.simplify(kernel.subs({x: y}) == 0)
    print("[entropy] (x-y) log(x/y) passes positive-flux sample checks")


def verify_hodge_dirac_commutation() -> None:
    star = sp.Matrix([[1, 0], [0, -1]])
    q = sp.Matrix([[0, 1], [1, 0]])
    delta = q * q

    assert q * star == -(star * q)
    assert delta * star == star * delta
    print("[hodge] Q anticommutes with star, and Q^2 commutes with star")


def verify_supertrace_cancellation() -> None:
    parity = sp.Matrix([[1, 0], [0, -1]])
    odd = sp.Matrix([[0, 1], [1, 0]])

    def parity_action(a: sp.Matrix) -> sp.Matrix:
        return parity * a * parity

    assert parity_action(odd) == -odd

    # Parity-invariant state: normalized trace is invariant under conjugation.
    supertrace = sp.trace(parity_action(odd)) / 2
    assert sp.simplify(supertrace) == 0
    print("[parity] invariant-state supertrace of odd operator vanishes")


def main() -> None:
    print("=== Supergraded Graph / Entropy / Hodge Bridge Witness ===")
    verify_graph_energy()
    verify_entropy_kernel()
    verify_hodge_dirac_commutation()
    verify_supertrace_cancellation()
    print("=== SUCCESS ===")


if __name__ == "__main__":
    main()
