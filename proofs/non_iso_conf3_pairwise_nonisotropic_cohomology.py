#!/usr/bin/env python3
"""Finite audit for pairwise non-isotropic Conf_3 quadric cohomology.

This mirrors the theorem-honest Lean layer:

* product/Leray candidate: (1+t)^3 (1+t^(D-1))^2, rank 32;
* OS-alpha candidate: (1+3t+2t^2) (1+t^(D-1))^2, rank 24;
* arity-three cooperad bookkeeping: each two-point collision has one
  internal edge and two outer edges.

It does not prove the analytic de Rham comparison theorem; that is the Lean
socket discharged by Dupont/Gysin/rank-decision hypotheses.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

import sympy as sp


t = sp.symbols("t")


def product_leray_poincare(D: int) -> sp.Expr:
    return sp.expand((1 + t) ** 3 * (1 + t ** (D - 1)) ** 2)


def os_alpha_poincare(D: int) -> sp.Expr:
    return sp.expand((1 + 3 * t + 2 * t**2) * (1 + t ** (D - 1)) ** 2)


def total_rank(poly: sp.Expr) -> int:
    return int(poly.subs(t, 1))


EDGES = ("12", "13", "23")
BLOCKS = {
    "12|3": "12",
    "13|2": "13",
    "23|1": "23",
}


@dataclass(frozen=True)
class CooperadImage:
    edge: str
    factor: str
    kind: str


def cooperad_edge(block: str, edge: str, kind: str) -> CooperadImage:
    internal_edge = BLOCKS[block]
    factor = "internal" if edge == internal_edge else "outer"
    return CooperadImage(edge=edge, factor=factor, kind=kind)


def verify_cooperad_bookkeeping() -> None:
    for block in BLOCKS:
        for kind in ("alpha", "beta"):
            images = [cooperad_edge(block, edge, kind) for edge in EDGES]
            internal = [img for img in images if img.factor == "internal"]
            outer = [img for img in images if img.factor == "outer"]
            assert len(internal) == 1, (block, kind, images)
            assert len(outer) == 2, (block, kind, images)
            assert internal[0].edge == BLOCKS[block]


def verify_basis_counts() -> None:
    product_basis = list(product((0, 1), repeat=5))
    os_alpha_basis = ["1", "a12", "a13", "a23", "a12a13", "a12a23"]
    flux_basis = list(product((0, 1), repeat=2))
    os_flux_basis = list(product(os_alpha_basis, flux_basis))
    assert len(product_basis) == 32
    assert len(os_flux_basis) == 24
    assert len(product_basis) - len(os_flux_basis) == 8


def main() -> None:
    verify_basis_counts()
    verify_cooperad_bookkeeping()

    for D in (4, 6, 8, 10):
        assert D % 2 == 0
        p_product = product_leray_poincare(D)
        p_os = os_alpha_poincare(D)
        assert total_rank(p_product) == 32
        assert total_rank(p_os) == 24
        print(f"D={D}")
        print(f"  product/Leray P(t) = {p_product}")
        print(f"  OS-alpha    P(t) = {p_os}")

    print("pairwise non-isotropic Conf3 finite cohomology/cooperad audit passed")
    print("selected finite branch under rank-decision/log-potential socket: productLeray")


if __name__ == "__main__":
    main()

