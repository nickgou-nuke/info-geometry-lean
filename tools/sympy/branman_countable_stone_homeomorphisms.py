#!/usr/bin/env python3
"""Finite exact witness for the homeomorphism-group skeleton of a finite Stone space."""

from __future__ import annotations

import itertools
import json
import math

import sympy as sp


def permutations(n: int):
    return list(itertools.permutations(range(n)))


def compose(p, q):
    return tuple(p[i] for i in q)


def inverse(p):
    inv = [0] * len(p)
    for i, j in enumerate(p):
        inv[j] = i
    return tuple(inv)


def main() -> None:
    n = 4
    perms = permutations(n)
    identity = tuple(range(n))

    assert len(perms) == math.factorial(n)
    assert identity in perms

    closure_checks = 0
    inverse_checks = 0
    for p in perms:
        inv = inverse(p)
        inverse_checks += 1
        assert inv in perms
        assert compose(p, inv) == identity
        assert compose(inv, p) == identity
        for q in perms:
            closure_checks += 1
            assert compose(p, q) in perms

    # Exact count for the group of self-homeomorphisms of a finite discrete Stone space.
    group_order = sp.factorial(n)
    assert group_order == 24

    print(
        json.dumps(
            {
                "certificate": "branman_countable_stone_homeomorphisms",
                "stone_space_size": n,
                "homeomorphism_group_order": int(group_order),
                "closure_checks": closure_checks,
                "inverse_checks": inverse_checks,
                "interpretation": "finite discrete Stone space homeomorphisms are permutations",
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()

