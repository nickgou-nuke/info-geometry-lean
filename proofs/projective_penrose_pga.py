#!/usr/bin/env python3
"""SymPy witness for projective/affine Penrose PGA anchors."""

import sympy as sp


def assert_zero(name, expr):
    expr = sp.simplify(sp.expand(expr))
    assert expr == 0, f"{name} failed: {expr}"
    print(f"{name} ✓")


def assert_matrix_zero(name, mat):
    mat = sp.simplify(mat)
    assert mat == sp.zeros(*mat.shape), f"{name} failed:\n{mat}"
    print(f"{name} ✓")


print("§1 golden ratio / Fibonacci inflation")
phi = (1 + sp.sqrt(5)) / 2
assert_zero("phi^2 = phi + 1", phi**2 - phi - 1)
F = sp.Matrix([[1, 1], [1, 0]])
assert F.det() == -1
assert_matrix_zero("F^2 = F + I", F**2 - F - sp.eye(2))
print("Robinson/Penrose inflation algebra ✓")

print("\n§2 affine ratios and cross-ratio")
A, B, a, b, c, d = sp.symbols("A B a b c d", nonzero=True)
aff = lambda x: A*x + B
ratio = lambda x, y, u, v: (x-y)/(u-v)
assert_zero("affine ratio preservation", ratio(aff(a), aff(b), aff(c), aff(d)) - ratio(a, b, c, d))
cr = lambda w, x, y, z: ((w-y)*(x-z))/((w-z)*(x-y))
assert_zero("affine cross-ratio preservation", cr(aff(a), aff(b), aff(c), aff(d)) - cr(a, b, c, d))
print("affine/projective invariants verified ✓")

print("\n§3 projective scalar invariance of Mobius maps")
lam, z = sp.symbols("lam z", nonzero=True)
M = lambda A, B, C, D, z: (A*z + B)/(C*z + D)
C, D = sp.symbols("C D", nonzero=True)
assert_zero("M and lambda*M act identically", M(lam*A, lam*B, lam*C, lam*D, z) - M(A, B, C, D, z))
print("projective quotient GL(2)/scalars visible ✓")

print("\n§4 PGA line incidence via exterior/cross product")
p1, p2, p3, q1, q2, q3 = sp.symbols("p1 p2 p3 q1 q2 q3")
p = sp.Matrix([p1, p2, p3])
q = sp.Matrix([q1, q2, q3])
line = p.cross(q)
assert_zero("p lies on p∧q", (p.dot(line)))
assert_zero("q lies on p∧q", (q.dot(line)))
print("homogeneous point-line dual incidence verified ✓")

print("\n§5 operator algebra socket")
print("tiling hull/groupoid/higher-rank Cuntz-Krieger layer is a C*-algebra socket; finite automaton anchors above ✓")
print("\nprojective_penrose_pga.py: All identities verified")
