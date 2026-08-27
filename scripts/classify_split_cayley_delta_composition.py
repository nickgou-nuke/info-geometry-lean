#!/usr/bin/env python3
"""Finite CAS classification for the elementary split-Cayley maps.

This is exploratory evidence only: Lean remains the proof authority.  It
records exactly when the tempting additive parameter law holds and produces a
small counterexample when it does not.
"""
from itertools import product

F = range(2)
V = list(product(F, repeat=3))
O = list(product(F, V, V, F))

def addv(x, y): return tuple((a + b) % 2 for a, b in zip(x, y))
def dot(x, y): return sum(a*b for a, b in zip(x, y)) % 2
def cross(x, y):
    return ((x[1]*y[2] + x[2]*y[1]) % 2,
            (x[2]*y[0] + x[0]*y[2]) % 2,
            (x[0]*y[1] + x[1]*y[0]) % 2)

def delta1(r, x):
    a, u, v, b = x
    rv = dot(r, v)
    return ((a-rv) % 2,
            tuple(((a-b-rv)*r[i] + u[i]) % 2 for i in range(3)),
            tuple((v[i] - cross(u, r)[i]) % 2 for i in range(3)),
            (b+rv) % 2)

def delta2(r, x):
    a, u, v, b = x
    ur = dot(u, r)
    return ((a+ur) % 2,
            tuple((u[i] + cross(v, r)[i]) % 2 for i in range(3)),
            tuple(((-a+b-ur)*r[i] + v[i]) % 2 for i in range(3)),
            (b-ur) % 2)

def add_parameter(r, s): return addv(r, s)

for name, f in (("delta1", delta1), ("delta2", delta2)):
    true_pairs = []
    counterexample = None
    for r in V:
        for s in V:
            ok = all(f(r, f(s, x)) == f(add_parameter(r, s), x) for x in O)
            if ok:
                true_pairs.append((r, s))
            elif counterexample is None:
                x = next(x for x in O if f(r, f(s, x)) != f(add_parameter(r, s), x))
                counterexample = (r, s, x, f(r, f(s, x)), f(add_parameter(r, s), x))
    print(f"{name}: additive-law pairs = {len(true_pairs)}/{len(V)*len(V)}")
    expected = [(r, s) for r in V for s in V
                if r == (0, 0, 0) or s == (0, 0, 0) or r == s]
    print(f"{name}: trivial-condition pairs = {len(expected)}")
    print(f"{name}: exact trivial-condition classification = {true_pairs == expected}")
    print(f"{name}: first counterexample = {counterexample}")

for name, f in (("delta1", delta1), ("delta2", delta2)):
    commuting = []
    for i in range(3):
        for j in range(i + 1, 3):
            ei = tuple(1 if k == i else 0 for k in range(3))
            ej = tuple(1 if k == j else 0 for k in range(3))
            if all(f(ei, f(ej, x)) == f(ej, f(ei, x)) for x in O):
                commuting.append((i, j))
    print(f"{name}: commuting distinct basis pairs = {commuting}")
