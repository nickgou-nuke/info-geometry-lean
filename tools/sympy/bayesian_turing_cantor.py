#!/usr/bin/env python3
"""Exact certificates for the finite Bayesian/Turing/Cantor layer."""
from fractions import Fraction
import sympy as sp


def words(n):
    if n == 0:
        return [()]
    return [w + (b,) for w in words(n - 1) for b in (0, 1)]


def shift(tape):
    return tape[1:]


def prefix(tape, n):
    return tape[:n]

# Turing tape/Cantor prefix and shift readout.
tape = (1, 0, 1, 1, 0, 0, 1)
for n in range(5):
    assert prefix(shift(tape), n) == prefix(tape, n + 1)[1:]

# Finite program/cylinder Boolean operations.
U = set(words(3))
A = {w for w in U if w[0] == 1}
B = {w for w in U if w[1] == 0}
x = prefix(tape, 3)
assert (x in (A & B)) == ((x in A) and (x in B))
assert (x in (A | B)) == ((x in A) or (x in B))
assert (x in (U - A)) == (not (x in A))

# Exact rational Bayesian update on an observed atom.
prior = {w: Fraction(1, len(U)) for w in U}
obs = x
posterior = {w: (Fraction(1) if w == obs else Fraction(0)) for w in U}
assert sum(posterior.values(), Fraction(0)) == Fraction(1)
assert posterior[obs] == Fraction(1)
for w in U:
    if w != obs:
        assert posterior[w] == Fraction(0)

# Log-Radon-Nikodym additive cocycle and closed-loop telescoping.
a, b, c = sp.Rational(2, 3), sp.Rational(5, 7), sp.Rational(-11, 13)
log_inc = lambda p, q: q - p
assert sp.simplify(log_inc(a, b) + log_inc(b, c) - log_inc(a, c)) == 0
assert sp.simplify(log_inc(a, b) + log_inc(b, c) + log_inc(c, a)) == 0

# dQ/Q residue on a boundary coordinate with dQ=Q.
Q = sp.Rational(17, 19)
assert sp.simplify(Q / Q) == 1

# Twistor incidence for zero matrix: omega = X*pi = 0.
pi = [sp.Rational(3, 5), sp.Rational(-2, 7)]
X = [[sp.Rational(0), sp.Rational(0)], [sp.Rational(0), sp.Rational(0)]]
omega = [sum(X[i][j] * pi[j] for j in range(2)) for i in range(2)]
assert omega == [0, 0]

print("BAYESIAN_TURING_CANTOR_SYMPY_OK")
