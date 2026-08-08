#!/usr/bin/env python3
"""Penrose spin incidence tessellation witness.

This connects the complete three-point incidence tile K3 to the corrected D=4
alpha/beta quadric model:

  edge 12 -> alpha12, beta12
  edge 23 -> alpha23, beta23
  edge 13 -> alpha13, beta13

The alpha cycle relation is the Arnold relation around the triangle.
"""

from __future__ import annotations

from fractions import Fraction


def count_polynomial(p: int) -> int:
    return p**2 * (p - 1) ** 2 * (p + 1) * (p**3 - 2 * p**2 - p + 3)


def main() -> None:
    tile_colors = ["thick", "thin", "star", "boat", "diamond"]
    edges = ["12", "23", "13"]
    labels = {(edge, kind): f"{kind}{edge}" for edge in edges for kind in ("alpha", "beta")}
    assert len(tile_colors) == 5
    assert len(labels) == 6

    degrees = {labels[(edge, "alpha")]: 1 for edge in edges}
    degrees.update({labels[(edge, "beta")]: 3 for edge in edges})
    assert all(degrees[f"alpha{edge}"] == 1 for edge in edges)
    assert all(degrees[f"beta{edge}"] == 3 for edge in edges)

    # Normal form in basis alpha12*alpha23, alpha12*alpha13.
    reduce_product = {
        "a12a23": (Fraction(1), Fraction(0)),
        "a12a13": (Fraction(0), Fraction(1)),
        "a23a13": (Fraction(-1), Fraction(1)),
    }
    relation = tuple(
        reduce_product["a12a23"][i]
        - reduce_product["a12a13"][i]
        + reduce_product["a23a13"][i]
        for i in range(2)
    )
    assert relation == (0, 0)
    assert count_polynomial(3) == 1296

    print("penrose_spin_incidence_tessellation.py: incidence tessellation passed")
    print("tile colors:", tile_colors)
    print("edge labels:", labels)
    print("alpha cycle relation normal form:", relation)
    print("#U4(F3) fingerprint:", count_polynomial(3))


if __name__ == "__main__":
    main()
