#!/usr/bin/env python3
"""Exact finite witness for the Cantor-style finite-cylinder basis.

This is a finite, exact-rational sanity check for the Mathlib product-topology
layer in ``PiCylinderMathlib`` / ``CantorCylinderTopology``.

It verifies on a small finite Boolean cube that:
* cylinders are defined by coordinate agreement on a finite index set;
* a cylinder is the intersection of the singleton coordinate cylinders;
* the target point belongs to its own cylinder;
* the intersection of all finite cylinders through a point isolates that point.
"""

from __future__ import annotations

import json
from itertools import product
from sympy import Rational


def all_points(n: int):
    return list(product([0, 1], repeat=n))


def cylinder(f, s):
    return {g for g in all_points(len(f)) if all(g[i] == f[i] for i in s)}


def finite_cylinder_certificate(max_n: int = 5):
    payload = {
        "certificate": "countable_stone_cylinder_basis",
        "max_n": max_n,
        "checks": [],
    }

    for n in range(1, max_n + 1):
        pts = all_points(n)
        for f in pts:
            # singleton coordinate cylinders
            for i in range(n):
                c = cylinder(f, {i})
                assert f in c
                for g in pts:
                    if g in c:
                        assert g[i] == f[i]
            # finite cylinders: full coordinate agreement gives singleton
            c_full = cylinder(f, set(range(n)))
            assert c_full == {f}
            # intersection over coordinate cylinders
            inter = set(pts)
            for i in range(n):
                inter &= cylinder(f, {i})
            assert inter == {f}
        payload["checks"].append({
            "n": n,
            "num_points": len(pts),
            "uniform_mass": str(Rational(1, len(pts))),
        })

    return payload


if __name__ == "__main__":
    print(json.dumps(finite_cylinder_certificate(), sort_keys=True))

