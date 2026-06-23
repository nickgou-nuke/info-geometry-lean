"""Finite witness for the twistor/amplituhedron interface layer.

This script checks only the algebra mirrored by
`TwistorAmplituhedronConfigurationBridge.lean`:

* three concrete Pluecker lines lie on the Klein quadric;
* the three line pairs have nonzero Klein incidence pairing;
* the configured local rank and spin-tiling multiplicity give 32.

It does not prove an amplituhedron theorem, BCFW recursion, plabic equivalence,
or an N=4 SYM state-count theorem.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Iterable

import sympy as sp


@dataclass(frozen=True)
class Vec4:
    x0: sp.Expr
    x1: sp.Expr
    x2: sp.Expr
    x3: sp.Expr

    def as_tuple(self) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
        return (self.x0, self.x1, self.x2, self.x3)


@dataclass(frozen=True)
class Plucker6:
    p01: sp.Expr
    p02: sp.Expr
    p03: sp.Expr
    p12: sp.Expr
    p13: sp.Expr
    p23: sp.Expr

    def as_tuple(self) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
        return (self.p01, self.p02, self.p03, self.p12, self.p13, self.p23)


def wedge(u: Vec4, v: Vec4) -> Plucker6:
    a = u.as_tuple()
    b = v.as_tuple()
    return Plucker6(
        a[0] * b[1] - a[1] * b[0],
        a[0] * b[2] - a[2] * b[0],
        a[0] * b[3] - a[3] * b[0],
        a[1] * b[2] - a[2] * b[1],
        a[1] * b[3] - a[3] * b[1],
        a[2] * b[3] - a[3] * b[2],
    )


def klein_q(P: Plucker6) -> sp.Expr:
    return sp.expand(P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12)


def incidence(P: Plucker6, Q: Plucker6) -> sp.Expr:
    return sp.expand(
        P.p01 * Q.p23
        - P.p02 * Q.p13
        + P.p03 * Q.p12
        + P.p12 * Q.p03
        - P.p13 * Q.p02
        + P.p23 * Q.p01
    )


def pair_indices(n: int) -> Iterable[tuple[int, int]]:
    for i in range(n):
        for j in range(i + 1, n):
            yield i, j


def main() -> None:
    e0 = Vec4(1, 0, 0, 0)
    e1 = Vec4(0, 1, 0, 0)
    e2 = Vec4(0, 0, 1, 0)
    e3 = Vec4(0, 0, 0, 1)

    # Three standard pairwise-skew projective lines in P^3:
    # span(e0,e1), span(e2,e3), span(e0+e2,e1+e3).
    lines = [
        wedge(e0, e1),
        wedge(e2, e3),
        wedge(Vec4(1, 0, 1, 0), Vec4(0, 1, 0, 1)),
    ]

    klein_checks = [sp.simplify(klein_q(P)) == 0 for P in lines]
    incidence_values = {
        f"{i}{j}": sp.simplify(incidence(lines[i], lines[j]))
        for i, j in pair_indices(len(lines))
    }
    nonincident_checks = {key: value != 0 for key, value in incidence_values.items()}

    betti_numbers = [1, 2, 1, 1, 2, 1, 0, 0, 0]
    local_rank = sum(betti_numbers)
    spin_tiling_multiplicity = 4
    state_budget = 32
    rank_budget_ok = local_rank * spin_tiling_multiplicity == state_budget

    checks = {
        "klein_lines": all(klein_checks),
        "pairwise_nonincident": all(nonincident_checks.values()),
        "rank_budget": rank_budget_ok,
    }
    if not all(checks.values()):
        raise AssertionError(
            {
                "checks": checks,
                "klein": [klein_q(P) for P in lines],
                "incidence": incidence_values,
            }
        )

    print("TWISTOR_AMPLITUHEDRON_INTERFACE_WITNESS_OK")
    print(
        json.dumps(
            {
                "checks": checks,
                "incidence_values": {k: str(v) for k, v in incidence_values.items()},
                "local_rank": local_rank,
                "spin_tiling_multiplicity": spin_tiling_multiplicity,
                "state_budget": state_budget,
                "scope": (
                    "finite Pluecker/Klein incidence and rank-budget arithmetic only; "
                    "no amplituhedron, BCFW, plabic, or N=4 SYM theorem asserted"
                ),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
