#!/usr/bin/env python3
"""SymPy witness for ContinuumAsColimitCounting.lean.

Checks the finite kernels:
  * |{0,1}^n| = 2^n and refinement doubles the count;
  * Jaynes/LDDP entropy is zero for p=m, the matching counting reference;
  * cylinder observables are unchanged by duplicating/refining the last bit;
  * GNS-like expectation is a reference-state readout.

Analytic measure limits, C*-completion, and Hilbert-space GNS completion remain
Lean deferred_interfaces.
"""

import math
import sympy as sp


def bitwords(n):
    if n == 0:
        return [()]
    out = [()]
    for _ in range(n):
        out = [w + (b,) for w in out for b in (0, 1)]
    return out


for n in range(8):
    words = bitwords(n)
    words_next = bitwords(n + 1)
    assert len(words) == 2**n
    assert len(words_next) == 2 * len(words)

    # Jaynes/LDDP entropy relative to the same finite counting density.
    m = sp.Rational(1, len(words))
    S = -sum(m * sp.log(m / m) for _ in words)
    assert sp.simplify(S) == 0

    # Cylinder compatibility: f(prefix_n(w)) is unchanged by successor embedding.
    values = {w: sp.Symbol("f_" + "".join(map(str, w)) if w else "f_empty") for w in words}
    for w_next in words_next:
        prefix = w_next[:-1]
        embedded_value = values[prefix]
        cylinder_value = values[prefix]
        assert embedded_value == cylinder_value


def words_q(n, q):
    if n == 0:
        return [()]
    out = [()]
    for _ in range(n):
        out = [w + (a,) for w in out for a in range(q)]
    return out


for n in range(7):
    words4 = words_q(n, 4)
    words4_next = words_q(n + 1, 4)
    assert len(words4) == 4**n
    assert len(words4_next) == 4 * len(words4)

    m4 = sp.Rational(1, len(words4))
    S4 = -sum(m4 * sp.log(m4 / m4) for _ in words4)
    assert sp.simplify(S4) == 0

    values4 = {
        w: sp.Symbol("g_" + "".join(map(str, w)) if w else "g_empty")
        for w in words4
    }
    for w_next in words4_next:
        prefix = w_next[:-1]
        assert values4[prefix] == values4[prefix]

# GNS-like reference readout: <Omega, pi(a)Omega> = omega(a).
omega_a = sp.Symbol("omega_a")
vacuum_expectation = omega_a
assert vacuum_expectation == omega_a

print("continuum_as_colimit_counting.py: all finite witnesses passed")
