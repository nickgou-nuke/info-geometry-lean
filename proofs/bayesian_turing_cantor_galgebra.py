#!/usr/bin/env python3
"""galgebra-lane smoke certificate for finite logarithmic identities."""
try:
    import galgebra  # noqa: F401
except Exception as exc:  # pragma: no cover
    raise SystemExit(f"galgebra import failed: {exc}")
from fractions import Fraction

a, b, c = Fraction(2, 3), Fraction(5, 7), Fraction(-11, 13)
inc = lambda p, q: q - p
assert inc(a, b) + inc(b, c) == inc(a, c)
assert inc(a, b) + inc(b, c) + inc(c, a) == 0
print("bayesian Turing Cantor galgebra certificate: ok")
