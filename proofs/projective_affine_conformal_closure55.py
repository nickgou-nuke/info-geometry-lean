#!/usr/bin/env python3
"""SymPy witness for ProjectiveAffineConformalClosure55.lean.

Finite audit for the projective affine conformal closure:
  R^(4,4) --x ↦ (x,(1-Q)/2,(1+Q)/2)--> null cone in R^(5,5)
  Q55 = Q44 + u^2 - v^2
  elementary O(5,5) reflections preserve Q55
  spectral CPT s ↦ 1-conj(s) fixes Re(s)=1/2

Pin(5,5), full Clifford action, and Cantor/Cuntz boundary realization remain
explicit sockets in Lean.
"""

import sympy as sp

x0, x1, x2, x3, y0, y1, y2, y3 = sp.symbols("x0 x1 x2 x3 y0 y1 y2 y3", real=True)
u, v = sp.symbols("u v", real=True)
a, b = sp.symbols("a b", real=True)

Q44 = x0**2 + x1**2 + x2**2 + x3**2 - (y0**2 + y1**2 + y2**2 + y3**2)
U = (1 - Q44) / 2
V = (1 + Q44) / 2
Q55_embed = Q44 + U**2 - V**2
assert sp.expand(Q55_embed) == 0

Q55 = x0**2 + x1**2 + x2**2 + x3**2 + u**2 - (y0**2 + y1**2 + y2**2 + y3**2 + v**2)
Q55_reflect_u = x0**2 + x1**2 + x2**2 + x3**2 + (-u)**2 - (y0**2 + y1**2 + y2**2 + y3**2 + v**2)
Q55_reflect_v = x0**2 + x1**2 + x2**2 + x3**2 + u**2 - (y0**2 + y1**2 + y2**2 + y3**2 + (-v)**2)
assert sp.expand(Q55_reflect_u - Q55) == 0
assert sp.expand(Q55_reflect_v - Q55) == 0

# Projective rescaling: Q55(λX)=λ²Q55(X).
lam = sp.symbols("lam", real=True, nonzero=True)
Q55_scaled = (lam*x0)**2 + (lam*x1)**2 + (lam*x2)**2 + (lam*x3)**2 + (lam*u)**2 - (
    (lam*y0)**2 + (lam*y1)**2 + (lam*y2)**2 + (lam*y3)**2 + (lam*v)**2
)
assert sp.expand(Q55_scaled - lam**2 * Q55) == 0

# Spectral CPT: s = a + ib maps to 1-a + ib; fixed iff a=1/2.
s = a + sp.I*b
cpt = 1 - sp.conjugate(s)
assert sp.simplify(sp.re(cpt) - (1 - a)) == 0
assert sp.simplify(sp.im(cpt) - b) == 0
fixed_real_solution = sp.solve(sp.Eq(1 - a, a), a)[0]
assert fixed_real_solution == sp.Rational(1, 2)

print("projective_affine_conformal_closure55.py: all witnesses passed")
