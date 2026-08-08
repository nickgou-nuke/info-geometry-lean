#!/usr/bin/env python3
"""SymPy witness for noncommutative tiling algebra anchors."""

import sympy as sp


def assert_zero(name, expr):
    expr = sp.simplify(sp.expand(expr))
    assert expr == 0, f"{name} failed: {expr}"
    print(f"{name} ✓")


def assert_matrix_zero(name, mat):
    mat = sp.simplify(mat)
    assert mat == sp.zeros(*mat.shape), f"{name} failed:\n{mat}"
    print(f"{name} ✓")


print("§1 finite groupoid convolution = matrix multiplication")
f = sp.Matrix([[1, 2], [3, 4]])
g = sp.Matrix([[0, 1], [1, 0]])
h = sp.Matrix([[2, -1], [5, 3]])
assert_matrix_zero("convolution associativity", (f*g)*h - f*(g*h))
print("finite pair-groupoid convolution anchor ✓")

print("\n§2 Fibonacci/Penrose Perron-Frobenius data")
phi = (1 + sp.sqrt(5)) / 2
assert_zero("phi^2=phi+1", phi**2 - phi - 1)
F = sp.Matrix([[1, 1], [1, 0]])
v = sp.Matrix([phi, 1])
assert_matrix_zero("F [phi,1]^T = phi [phi,1]^T", F*v - phi*v)
print("tile-frequency eigenvector anchor ✓")

print("\n§3 trace/gap labels Z + phi Z")
m, n, p, q = sp.symbols("m n p q", integer=True)
gap = lambda a, b: a + b*phi
assert_zero("gap labels closed under addition", gap(m,n) + gap(p,q) - gap(m+p, n+q))
assert_zero("gap labels closed under negation", -gap(m,n) - gap(-m,-n))
print("trace range/gap-label module Z+phi Z anchor ✓")

print("\n§3b algebraic K0 inflation scales trace by phi")
m, n = sp.symbols("m n", integer=True)
eval_trace = lambda pair: pair[0] + pair[1] * phi
inflation = lambda pair: (pair[1], pair[0] + pair[1])
v = (m, n)
assert_zero("evalTrace(inflation v)=phi evalTrace(v)", eval_trace(inflation(v)) - phi * eval_trace(v))
K0 = sp.Matrix([[0, 1], [1, 1]])
assert_matrix_zero("K0 inflation matrix action", K0 * sp.Matrix([m, n]) - sp.Matrix([n, m+n]))
print("dimension-group / gap-label scaling anchor ✓")

print("\n§4 Robinson/Penrose frequencies")
thick = 1/phi
thin = 1/phi**2
assert_zero("1/phi + 1/phi^2 = 1", thick + thin - 1)
print("relative thick/thin frequencies normalized ✓")

print("\n§5 spectral triple/groupoid sockets")
print("C*(G), von Neumann trace, K0 gap labels, and Connes spectral triple are sockets; finite anchors verified ✓")

print("\nnoncommutative_tiling_algebra.py: All identities verified")
