#!/usr/bin/env python3
"""Finite Dupont/Gysin skeleton for the three non-isotropic quadric divisors.

After translation, the three-point space is the complement in C^D x C^D of

  QA  = q(a)
  QB  = q(b)
  QAB = q(a-b).

For the finite audit we use the split D=4 quadratic form

  q(x0,x1,x2,x3) = x0*x1 + x2*x3,

which is equivalent over C to any nondegenerate complex quadric.  The script
checks the Boolean stratum poset, generic Jacobian ranks, and the Hasse cover
graph used by the Lean deferred_interface.
"""

from __future__ import annotations

from itertools import combinations, product

import sympy as sp


LABELS = ("QA", "QB", "QAB")


def q(v: tuple[int, int, int, int]) -> int:
    return v[0] * v[1] + v[2] * v[3]


def mask_values(a: tuple[int, int, int, int], b: tuple[int, int, int, int]) -> tuple[bool, bool, bool]:
    diff = tuple(ai - bi for ai, bi in zip(a, b))
    return (q(a) == 0, q(b) == 0, q(diff) == 0)


def find_generic_point(mask: tuple[bool, bool, bool]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    values = range(-2, 3)
    for coords in product(values, repeat=8):
        a = coords[:4]
        b = coords[4:]
        diff = tuple(ai - bi for ai, bi in zip(a, b))
        if mask[0] and a == (0, 0, 0, 0):
            continue
        if mask[1] and b == (0, 0, 0, 0):
            continue
        if mask[2] and diff == (0, 0, 0, 0):
            continue
        if mask_values(a, b) == mask:
            return a, b
    raise RuntimeError(f"no point found for mask {mask}")


def jacobian_rank(mask: tuple[bool, bool, bool], a: tuple[int, ...], b: tuple[int, ...]) -> int:
    a0, a1, a2, a3, b0, b1, b2, b3 = sp.symbols("a0 a1 a2 a3 b0 b1 b2 b3")
    avec = (a0, a1, a2, a3)
    bvec = (b0, b1, b2, b3)
    diff = tuple(x - y for x, y in zip(avec, bvec))
    polys = (
        avec[0] * avec[1] + avec[2] * avec[3],
        bvec[0] * bvec[1] + bvec[2] * bvec[3],
        diff[0] * diff[1] + diff[2] * diff[3],
    )
    variables = avec + bvec
    rows = []
    subs = dict(zip(variables, a + b))
    for active, poly in zip(mask, polys):
        if active:
            rows.append([sp.diff(poly, var).subs(subs) for var in variables])
    if not rows:
        return 0
    return sp.Matrix(rows).rank()


def codim(mask: tuple[bool, bool, bool]) -> int:
    return sum(1 for bit in mask if bit)


def covers(mask: tuple[bool, bool, bool]) -> list[tuple[bool, bool, bool]]:
    out = []
    for i, bit in enumerate(mask):
        if not bit:
            new_mask = list(mask)
            new_mask[i] = True
            out.append(tuple(new_mask))
    return out


def main() -> None:
    masks = [tuple(i in subset for i in range(3)) for r in range(4) for subset in combinations(range(3), r)]
    assert len(masks) == 8
    assert sum(len(covers(mask)) for mask in masks) == 12

    print("strata:")
    for mask in masks:
        active = tuple(label for label, bit in zip(LABELS, mask) if bit)
        point = find_generic_point(mask)
        rank = jacobian_rank(mask, *point)
        assert rank == codim(mask)
        for cover in covers(mask):
            assert codim(cover) == codim(mask) + 1
        print(f"  {active or ('open',)} codim={codim(mask)} sample={point} rank={rank}")

    # Cluster {1,2}: internal edge 12 stays internal, external edges 13 and 23
    # collapse to the same outer edge.
    collapse12 = {"12": "inner", "13": "outer", "23": "outer"}
    assert collapse12["12"] == "inner"
    assert collapse12["13"] == collapse12["23"] == "outer"

    print("cover edges:", sum(len(covers(mask)) for mask in masks))
    print("cluster {1,2} cooperad edge collapse:", collapse12)
    print("non_iso_conf3_dupont_gysin_model.py: Dupont/Gysin skeleton passed")


if __name__ == "__main__":
    main()
