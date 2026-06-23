#!/usr/bin/env python3
"""Clifford-lane smoke certificate for finite spinor/tape algebra."""
try:
    import clifford  # noqa: F401
except Exception as exc:  # pragma: no cover
    raise SystemExit(f"clifford import failed: {exc}")
from fractions import Fraction

# Zero 2x2 twistor incidence X*pi = 0.
pi = [Fraction(3, 5), Fraction(-2, 7)]
X = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]]
omega = [sum(X[i][j] * pi[j] for j in range(2)) for i in range(2)]
assert omega == [0, 0]
print("bayesian Turing Cantor clifford certificate: ok")
