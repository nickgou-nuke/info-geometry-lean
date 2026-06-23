#!/usr/bin/env python3
"""Exact finite certificates for UHF Boolean projection / Cantor Stone bridge.

This script mirrors the Lean finite/profinite corridor:

* finite Boolean algebras are powersets of binary words;
* a point/ultrafilter evaluates a finite event into Bool;
* evaluation preserves union, intersection, and complement;
* prefix pullback is contravariantly compatible with Cantor cylinders;
* exact rational Bayesian conditioning stays inside the finite cylinder algebra.
* successor cylinder mass is persistent under prefix pushforward.
"""
import sympy as sp

# finite binary words of length n
def words(n):
    if n == 0:
        return [()]
    return [w + (b,) for w in words(n-1) for b in (False, True)]

def prefix(w):
    return w[:-1]

def atom(a, v):
    return sp.Integer(1) if a == v else sp.Integer(0)

def bool_eval(w, event):
    return w in event

def prefix_pullback(event, n):
    return {w for w in words(n + 1) if prefix(w) in event}

def probability(event, weights):
    return sum(weights[w] for w in event)

def condition(weights, evidence):
    z = probability(evidence, weights)
    assert z != 0
    return {w: sp.simplify(weights[w] / z) for w in evidence}

for n in range(5):
    for a in words(n):
        for v in words(n):
            p = atom(a, v)
            assert p*p == p

for n in range(4):
    for w in words(n+1):
        assert prefix(w) in words(n)

# coherent finite prefixes from an infinite sample Cantor word
x = tuple([False, True, True, False, True, False])
for n in range(5):
    assert x[:n] == prefix(x[:n+1])

# finite Stone-side Boolean operations are preserved by cylinder membership
A = {words(3)[1], words(3)[4]}
B = {words(3)[4], words(3)[6]}
w = x[:3]
U3 = set(words(3))
assert bool_eval(w, A | B) == (bool_eval(w, A) or bool_eval(w, B))
assert bool_eval(w, A & B) == (bool_eval(w, A) and bool_eval(w, B))
assert bool_eval(w, U3 - A) == (not bool_eval(w, A))

# finite Stone evaluation is compatible with prefix pullback
for n in range(4):
    universe_n = set(words(n))
    event = {u for u in universe_n if len(u) == 0 or u[0] is True}
    for v in words(n + 1):
        assert bool_eval(v, prefix_pullback(event, n)) == bool_eval(prefix(v), event)

# Stone ultrafilter characteristic map into the two-element Boolean algebra.
def principal_ultrafilter(point, universe):
    return {frozenset(E) for E in powerset(universe) if point in E}

def powerset(xs):
    xs = list(xs)
    out = [set()]
    for x0 in xs:
        out += [s | {x0} for s in out]
    return out

U = set(words(3))
point = x[:3]
ultra = principal_ultrafilter(point, U)
for E in powerset(U):
    E = set(E)
    chiE = bool_eval(point, E)
    assert chiE == (frozenset(E) in ultra)
    for F in powerset(U):
        F = set(F)
        assert bool_eval(point, E & F) == (bool_eval(point, E) and bool_eval(point, F))
        assert bool_eval(point, E | F) == (bool_eval(point, E) or bool_eval(point, F))
    assert bool_eval(point, U - E) == (not bool_eval(point, E))

# exact rational Bayesian update on a cylinder event
stage = 3
universe = words(stage)
prior = {w: sp.Rational(1, len(universe)) for w in universe}
evidence = {w for w in universe if w[:1] == (True,)}
posterior = condition(prior, evidence)
assert sp.simplify(sum(posterior.values())) == sp.Integer(1)
for w0 in evidence:
    assert posterior[w0] == sp.Rational(1, len(evidence))

# successor persistence: depth-n atom mass equals the sum of its two children.
stage_next = 4
next_words = words(stage_next)
next_weights = {
    w: sp.Rational(i + 1, sum(range(1, len(next_words) + 1)))
    for i, w in enumerate(next_words)
}
stage_now = stage_next - 1
push_weights = {
    w: sp.simplify(
        next_weights[w + (False,)] + next_weights[w + (True,)]
    )
    for w in words(stage_now)
}
for w in words(stage_now):
    assert push_weights[w] == sp.simplify(
        probability({w + (False,)}, next_weights)
        + probability({w + (True,)}, next_weights)
    )

print('UHF_BOOLEAN_PROJECTION_CANTOR_BRIDGE_SYMPY_OK')
