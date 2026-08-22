#!/usr/bin/env python3
"""Symbolically derive the so(7) stabilizer of the standard G2 3-form."""

import sympy as sp
from itertools import combinations

triples = (
    ((0, 1, 2), 1), ((0, 3, 4), 1), ((0, 5, 6), 1),
    ((1, 3, 5), 1), ((1, 4, 6), -1), ((2, 3, 6), -1),
    ((2, 4, 5), -1),
)

def phi(i, j, k):
    if len({i, j, k}) < 3:
        return sp.Integer(0)
    target = tuple(sorted((i, j, k)))
    signed = dict(triples)
    if target not in signed:
        return sp.Integer(0)
    inversions = sum(a > b for n, a in enumerate((i, j, k)) for b in (i, j, k)[n + 1:])
    return signed[target] * sp.Integer(-1 if inversions % 2 else 1)

pairs = list(combinations(range(7), 2))
vars = sp.symbols(f'x0:{len(pairs)}')
A = sp.zeros(7)
for x, (i, j) in zip(vars, pairs):
    A[i, j] = x
    A[j, i] = -x

equations = []
for i, j, k in combinations(range(7), 3):
    equations.append(sp.expand(sum(
        A[i, p] * phi(p, j, k) +
        A[j, p] * phi(i, p, k) +
        A[k, p] * phi(i, j, p)
        for p in range(7))))

coefficient_matrix = sp.linear_eq_to_matrix(equations, vars)[0]
basis = coefficient_matrix.nullspace()
assert len(basis) == 14, len(basis)

print("G2_SO7_STABILIZER_DIM=14")
for n, vector in enumerate(basis):
    support = [(pairs[i], value) for i, value in enumerate(vector) if value]
    print(f"GENERATOR_{n}={support}")
print("SYMBOLIC_LINEAR_STABILIZER=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
