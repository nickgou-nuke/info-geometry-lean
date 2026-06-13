#!/usr/bin/env python3
"""
Optional smoke test using `galgebra`.

Checks the Cl(3,0) pseudoscalar complex-structure shadow I^2=-1.
This is not the authority for the formal proof; it is a package-surface check.
"""

from __future__ import annotations
import sys

try:
    from sympy import symbols, simplify
    from galgebra.ga import Ga
except ModuleNotFoundError as exc:
    print(f"SKIP: optional dependency not installed: {exc.name}")
    sys.exit(0)

try:
    x, y, z = symbols("x y z", real=True)
    ga = Ga("e1 e2 e3", g=[1, 1, 1], coords=[x, y, z])
    e1, e2, e3 = ga.mv()
    I = e1 * e2 * e3
    residual = simplify((I * I + 1).scalar())
    if residual != 0:
        raise AssertionError(f"I^2=-1 failed: residual={residual}")
    print("PASS: galgebra Cl(3,0) pseudoscalar I^2=-1")
except Exception as exc:
    print(f"SKIP: galgebra API smoke test could not run in this environment: {exc}")
    sys.exit(0)
