#!/usr/bin/env python3
"""
Optional smoke test using the `clifford` package.

The exact authority is tools/sympy/clifford_braiding_exact.py. This file is only
for checking that the package-level geometric-algebra surface agrees with the
exact symbolic Clifford braid relations.
"""

from __future__ import annotations
import sys

try:
    import numpy as np
    from clifford import Cl
except ModuleNotFoundError as exc:
    print(f"SKIP: optional dependency not installed: {exc.name}")
    sys.exit(0)


def close_zero(x, tol=1e-10):
    try:
        return np.max(np.abs(x.value)) < tol
    except Exception:
        return abs(float(x)) < tol


layout, blades = Cl(4)
e1, e2, e3, e4 = blades["e1"], blades["e2"], blades["e3"], blades["e4"]


def B(a, b):
    return (1 + a * b) / np.sqrt(2.0)

B0 = B(e1, e2)
B1 = B(e2, e3)
B2 = B(e3, e4)

checks = [
    ("B0^2=e1e2", B0*B0 - e1*e2),
    ("B0^4=-1", B0**4 + 1),
    ("B0^8=1", B0**8 - 1),
    ("Artin adjacent", B0*B1*B0 - B1*B0*B1),
    ("far commute", B0*B2 - B2*B0),
]

for name, residual in checks:
    if not close_zero(residual):
        raise AssertionError(f"{name} failed: {residual}")
    print(f"PASS: {name}")

print("Optional `clifford` smoke checks passed.")
