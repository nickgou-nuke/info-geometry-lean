#!/usr/bin/env python3
"""Exact finite certificate for Stone duality on a small powerset Boolean algebra."""

import itertools
import json
import sympy as sp


U = (0, 1, 2)
SUBSETS = [frozenset(s) for r in range(len(U) + 1) for s in itertools.combinations(U, r)]
TOP = frozenset(U)
BOT = frozenset()


def compl(A):
    return frozenset(x for x in U if x not in A)


def principal_ultrafilter(point):
    return {A for A in SUBSETS if point in A}


def characteristic(point):
    return {A: sp.Integer(1 if point in A else 0) for A in SUBSETS}


def preserves_bool_ops(h):
    for A in SUBSETS:
        assert h[A] in (sp.Integer(0), sp.Integer(1))
        assert h[TOP] == 1
        assert h[BOT] == 0
        assert h[compl(A)] == 1 - h[A]
        for B in SUBSETS:
            assert h[A & B] == h[A] * h[B]
            assert h[A | B] == max(h[A], h[B])
    return True


principal_checks = []
for p in U:
    uf = principal_ultrafilter(p)
    chi = characteristic(p)
    assert preserves_bool_ops(chi)
    assert {A for A in SUBSETS if chi[A] == 1} == uf
    principal_checks.append(p)


all_homs = []
for values in itertools.product([0, 1], repeat=len(SUBSETS)):
    h = {A: sp.Integer(v) for A, v in zip(SUBSETS, values)}
    try:
        if preserves_bool_ops(h):
            all_homs.append(h)
    except AssertionError:
        pass

principal_homs = [characteristic(p) for p in U]
assert len(all_homs) == len(principal_homs)
for h in all_homs:
    assert h in principal_homs

print(json.dumps({
    "certificate": "stone_duality_boolean_eval",
    "universe_size": len(U),
    "subset_count": len(SUBSETS),
    "principal_ultrafilters": len(principal_checks),
    "boolean_homomorphisms": len(all_homs),
    "two_element_boolean_algebra": [0, 1],
}, sort_keys=True))
