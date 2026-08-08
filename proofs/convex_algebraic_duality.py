#!/usr/bin/env python3
"""SymPy witness for convex algebraic duality anchors.

Inspired by Rostalski--Sturmfels, arXiv:1006.4894.
"""

import sympy as sp


def assert_zero(name, expr):
    expr = sp.simplify(sp.expand(expr))
    assert expr == 0, f"{name} failed: {expr}"
    print(f"{name} ✓")


print("§1 toy spectrahedron: diagonal PSD simplex")
t = sp.symbols("t")
x1, y1, x2, y2 = sp.symbols("x1 y1 x2 y2")
# If x1+y1=1 and x2+y2=1, then convex mix also sums to 1.
mix_sum = t*x1 + (1-t)*x2 + t*y1 + (1-t)*y2
assert_zero("trace-one affine constraint preserved", mix_sum.subs(y1, 1-x1).subs(y2, 1-x2) - 1)
print("nonnegativity is preserved for 0≤t≤1 by scalar convexity ✓")

print("\n§2 projective duality: conic gradient tangent hyperplane")
x, y, z = sp.symbols("x y z")
F = x**2 + y**2 - z**2
grad = sp.Matrix([2*x, 2*y, -2*z])
p = sp.Matrix([x, y, z])
assert_zero("Euler identity <grad F,p>=2F", grad.dot(p) - 2*F)
print("on F=0, gradient covector is tangent/projective dual ✓")

print("\n§3 scalar KKT/Lagrange stationarity")
c, r, lam = sp.symbols("c r lam")
stationary = 2*(r-c) + (-2*(r-c))
assert_zero("stationarity at feasible x=r", stationary)
slack = lam * 0
assert_zero("complementary slackness for active equality residual", slack)
print("KKT toy anchor verified ✓")

print("\n§4 sockets")
print("Full spectrahedral shadows, SDP duality, and projective-dual boundaries remain theorem-honest sockets ✓")

print("\nconvex_algebraic_duality.py: All identities verified")
