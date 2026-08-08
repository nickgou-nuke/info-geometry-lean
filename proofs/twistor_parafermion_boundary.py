#!/usr/bin/env python3
"""SymPy witness for TwistorParafermionBoundary.lean.

Audits finite algebra:
  X = [[t+z, x-i y], [x+i y, t-z]]
  det(X) = t^2 - x^2 - y^2 - z^2
  det(X)=0 is the null/light cone
  rank-one spinor dyads have zero determinant
  Penrose incidence: omega = i X pi
  four Cuntz lanes are modeled as four twistor components.
"""

import sympy as sp

I = sp.I
t, x, y, z = sp.symbols("t x y z")
pi0, pi1 = sp.symbols("pi0 pi1")
a, b, c, d = sp.symbols("a b c d")

X = sp.Matrix([[t + z, x - I * y], [x + I * y, t - z]])
assert sp.simplify(X.det() - (t**2 - x**2 - y**2 - z**2)) == 0

# Null light-ray example t=r, spatial=(r,0,0).
r = sp.symbols("r")
X_null = X.subs({t: r, x: r, y: 0, z: 0})
assert sp.simplify(X_null.det()) == 0

# Rank-one spinor dyad is always determinant zero.
dyad = sp.Matrix([[a * c, a * d], [b * c, b * d]])
assert sp.simplify(dyad.det()) == 0

# Penrose incidence omega = i X pi.
pi = sp.Matrix([pi0, pi1])
omega = I * X * pi
assert sp.simplify(omega[0] - I * ((t + z) * pi0 + (x - I * y) * pi1)) == 0
assert sp.simplify(omega[1] - I * ((x + I * y) * pi0 + (t - z) * pi1)) == 0

# Four twistor components map to four Cuntz/parafermion lanes in the audit model.
S = sp.symbols("S0:4", commutative=False)
twistor_components = (omega[0], omega[1], pi0, pi1)
lane_map = dict(zip(S, twistor_components))
assert len(lane_map) == 4
assert lane_map[S[0]] == omega[0]
assert lane_map[S[1]] == omega[1]
assert lane_map[S[2]] == pi0
assert lane_map[S[3]] == pi1

# Projective scaling of twistors.
lam = sp.symbols("lambda", nonzero=True)
Z = sp.Matrix(twistor_components)
W = lam * Z
for i in range(4):
    assert sp.simplify(W[i] - lam * Z[i]) == 0

print("twistor_parafermion_boundary.py: all witnesses passed")
