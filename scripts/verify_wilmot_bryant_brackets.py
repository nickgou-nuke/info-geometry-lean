#!/usr/bin/env python3
"""Exact CAS certificate for the 14 Bryant-Wilmot matrix generators.

The matrices are over Q.  The check is symbolic linear-algebra span
membership; it does not enumerate coefficient assignments or evaluate a
finite field model.
"""

import sympy as sp


def skew(i: int, j: int) -> sp.Matrix:
    m = sp.zeros(7)
    m[i, j] = 1
    m[j, i] = -1
    return m


def s(i: int, j: int) -> sp.Matrix:
    return skew(i, j)


half = sp.Rational(1, 2)
generators = [
    half * (s(1, 2) - s(3, 4)),
    half * (-s(0, 2) - s(3, 5)),
    half * (s(0, 1) + s(3, 6)),
    half * (s(0, 4) + s(1, 5)),
    half * (s(0, 3) - s(1, 6)),
    half * (s(0, 6) + s(1, 3)),
    half * (-s(0, 5) - s(1, 4)),
    half * (s(3, 4) - s(5, 6)),
    half * (s(3, 5) + s(4, 6)),
    half * (-s(3, 6) + s(4, 5)),
    half * (-s(1, 5) - s(2, 6)),
    half * (-s(1, 6) + s(2, 5)),
    half * (-s(0, 6) + s(2, 4)),
    half * (s(1, 4) - s(2, 3)),
]


def flatten(m: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([m[i, j] for i in range(7) for j in range(7)])


columns = sp.Matrix.hstack(*(flatten(m) for m in generators))
assert columns.rank() == 14

for i, left in enumerate(generators):
    for j, right in enumerate(generators):
        bracket = left * right - right * left
        solution = sp.linsolve((columns, flatten(bracket)))
        if solution == sp.EmptySet:
            raise AssertionError(f"bracket ({i},{j}) is outside the Bryant span")

print("BRYANT_GENERATOR_RANK=14")
print("BRYANT_BRACKET_CLOSURE_SYMBOLIC=PASS")
print("NO_ASSIGNMENT_ENUMERATION=PASS")
