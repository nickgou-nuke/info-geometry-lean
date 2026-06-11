#!/usr/bin/env python3
"""Finite Möbius/Witten/Weyl denominator witness.

Mirrors `InfoGeometry.Arithmetic.MobiusWittenWeylDenominator`.

The script verifies only finite cutoff identities:

    sum_{S subset P} (-1)^|S| prod_{p in S} q_p
      = prod_{p in P} (1 - q_p)

and the corresponding finite boson × fermion cancellation.  It does not claim
analytic convergence, an infinite Euler product, or a Riemann-zero theorem.
"""

from __future__ import annotations

from itertools import combinations

import sympy as sp


def powerset(items: list[int]):
    for r in range(len(items) + 1):
        yield from combinations(items, r)


def main() -> None:
    primes = [2, 3, 5, 7]
    q = {p: sp.symbols(f"q_{p}") for p in primes}

    mobius_supertrace = sp.Integer(0)
    for subset in powerset(primes):
        weight = sp.prod(q[p] for p in subset)
        mobius_supertrace += (-1) ** len(subset) * weight

    weyl_denominator = sp.prod(1 - q[p] for p in primes)
    bosonic_inverse = sp.prod((1 - q[p]) ** -1 for p in primes)

    print("--- finite Mobius/Witten/Weyl denominator witness ---")
    print(
        "1. Mobius supertrace equals Weyl denominator: "
        f"{sp.expand(mobius_supertrace - weyl_denominator) == 0}"
    )
    print(
        "2. Bosonic inverse times Mobius denominator cancels: "
        f"{sp.simplify(bosonic_inverse * weyl_denominator) == 1}"
    )
    print(
        "3. Expanded finite supertrace: "
        f"{sp.expand(mobius_supertrace)}"
    )
    print(
        "4. Factored Weyl denominator: "
        f"{sp.factor(weyl_denominator)}"
    )


if __name__ == "__main__":
    main()

