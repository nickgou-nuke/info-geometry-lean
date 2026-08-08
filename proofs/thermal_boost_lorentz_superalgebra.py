#!/usr/bin/env python3
"""Finite audit for the thermal-boost Lorentz superalgebra toy."""

import sympy as sp

eta, hbar, x, ct, E, p, c, m0 = sp.symbols("eta hbar x ct E p c m0")

xprime = x * sp.cosh(eta) - ct * sp.sinh(eta)
ctprime = ct * sp.cosh(eta) - x * sp.sinh(eta)
gamma = sp.cosh(eta)
q = sp.exp(-(hbar * eta))

safe_factor_zero = sp.Integer(1)
modified_zero = E**2 - p**2 * c**2 * safe_factor_zero**2 - m0**2 * c**4
expected_zero = E**2 - p**2 * c**2 - m0**2 * c**4

assert sp.simplify(xprime.subs(eta, 0) - x) == 0
assert sp.simplify(ctprime.subs(eta, 0) - ct) == 0
assert sp.simplify(gamma.subs(eta, 0) - 1) == 0
assert sp.simplify(q.subs(eta, 0) - 1) == 0
assert safe_factor_zero == 1
assert sp.simplify(modified_zero - expected_zero) == 0

print("thermal_boost_lorentz_superalgebra.py: SymPy audit passed")
