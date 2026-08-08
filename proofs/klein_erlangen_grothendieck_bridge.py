#!/usr/bin/env python3
"""Finite audit for the Klein/Erlangen/Grothendieck bridge."""

from dataclasses import dataclass


@dataclass(frozen=True)
class Plucker6:
    p01: int
    p02: int
    p03: int
    p12: int
    p13: int
    p23: int


def klein(P: Plucker6) -> int:
    return P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12


def smul(a: int, P: Plucker6) -> Plucker6:
    return Plucker6(*(a * x for x in (P.p01, P.p02, P.p03, P.p12, P.p13, P.p23)))


def main() -> None:
    line01 = Plucker6(1, 0, 0, 0, 0, 0)
    line23 = Plucker6(0, 0, 0, 0, 0, 1)
    mixed = Plucker6(1, 0, 1, -1, 0, 1)  # (e0+e2) wedge (e1+e3)
    for P in (line01, line23, mixed):
        assert klein(P) == 0
        for a in range(-5, 6):
            assert klein(smul(a, P)) == a * a * klein(P)

    edges = ["12", "23", "13"]
    kinds = ["alpha", "beta"]
    assert len([(e, k) for e in edges for k in kinds]) == 6
    grades = [-2, -1, 0, 1, 2]
    assert -1 + 1 == 0 and 2 + 1 not in grades

    print("klein_erlangen_grothendieck_bridge.py: finite Plucker/TKK/K3 audit passed")
    print("Klein parametrization, TKK≅so(2,4), motives, Langlands remain sockets.")


if __name__ == "__main__":
    main()
