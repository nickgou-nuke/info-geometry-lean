#!/usr/bin/env python3
"""
Exact SymPy/galgebra/clifford certificate for the theorem-safe geometric Stokes
boundary readout used by `GeometricStokes.lean`.

Certified facts:
- For A=(-y dx + x dy)/(x^2+y^2), the unit-circle line integral is exactly 2*pi.
- In galgebra and clifford, the planar bivector J=e1^e2 squares to -1.

No distributional Stokes theorem, GNS annihilation theorem, or global
Cantor-colimit theorem is claimed here.
"""

import os

os.environ.setdefault("NUMBA_DISABLE_JIT", "1")

import sympy as sp
from galgebra.ga import Ga
from clifford import Cl

# Exact line integral around the unit circle.
t = sp.symbols('t', real=True)
x = sp.cos(t)
y = sp.sin(t)
dx = sp.diff(x, t)
dy = sp.diff(y, t)
r2 = x**2 + y**2
integrand = sp.simplify((-y / r2) * dx + (x / r2) * dy)
angle = sp.integrate(integrand, (t, 0, 2 * sp.pi))
assert sp.simplify(integrand - 1) == 0
assert sp.simplify(angle - 2 * sp.pi) == 0

# galgebra: J^2=-1 in Cl(2,0).
ga = Ga('e*1|2', g=[1, 1])
e = ga.mv()
Jg = e[0] ^ e[1]
assert str(Jg * Jg) == '-1'

# clifford: J^2=-1 in Cl(2,0).
layout, blades = Cl(2, 0, firstIdx=1)
Jc = blades['e1'] ^ blades['e2']
assert Jc * Jc == -1

print('geometric_stokes_defect_sympy: exact angle 2*pi and J^2=-1 checks passed')
