#!/usr/bin/env python3
"""Exact finite-core checks for the Branman countable-Stone layer."""

import itertools
import math

import sympy as sp


def permutations(m):
    return list(itertools.permutations(range(m)))


# Finite discrete self-homeomorphisms are permutations.
for m in range(1, 7):
    assert len(permutations(m)) == math.factorial(m)


# Finite symmetric Cayley/CAR graph skeleton on Z/5Z.
modulus = 5
labels = {1, modulus - 1}


def adj(g, h):
    return ((h - g) % modulus) in labels


for f in labels:
    assert (-f) % modulus in labels

for g in range(modulus):
    for h in range(modulus):
        assert adj(g, h) == adj(h, g)
        for k in range(modulus):
            assert adj(g, h) == adj((k + g) % modulus, (k + h) % modulus)


# Polynomial exactness for inverse labels in the group algebra of C5.
x = sp.Symbol("x")
assert sp.rem(x * x**4 - 1, x**5 - 1, domain=sp.QQ) == 0
assert sp.rem(x**4 * x - 1, x**5 - 1, domain=sp.QQ) == 0

print("BRANMAN_COUNTABLE_STONE_FINITE_CORE_SYMPY_OK")
