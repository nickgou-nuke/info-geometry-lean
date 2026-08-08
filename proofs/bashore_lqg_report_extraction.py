#!/usr/bin/env python3
"""SymPy extraction witness for the Bashore LQG report.

Checks the finite algebraic spine extracted from
*Quantum Simulations of Spin Networks From the Perspective of Loop Quantum Gravity*.
"""

import sympy as sp

x, y, z, w = sp.symbols("x y z w", real=True)
a = x + sp.I * y
b = z + sp.I * w

U = sp.Matrix([[a, -sp.conjugate(b)], [b, sp.conjugate(a)]])
UU = sp.simplify(U.H * U)
r2 = x**2 + y**2 + z**2 + w**2

# Intertwiner qubit support from the report / Lean file.
support = [3, 5, 6, 9, 10, 12]
c0 = {5: sp.Rational(1, 2), 6: -sp.Rational(1, 2), 9: -sp.Rational(1, 2), 10: sp.Rational(1, 2)}
c1raw = {
    3: sp.Integer(1),
    12: sp.Integer(1),
    5: -sp.Rational(1, 2),
    6: -sp.Rational(1, 2),
    9: -sp.Rational(1, 2),
    10: -sp.Rational(1, 2),
}


def coeff(table, n):
    return table.get(n, sp.Integer(0))


def dot(a_, b_):
    return sp.simplify(sum(coeff(a_, n) * coeff(b_, n) for n in support))


norm0 = dot(c0, c0)
norm1raw = dot(c1raw, c1raw)
orth = dot(c0, c1raw)

# Finite LQG/NMR bookkeeping.
qubits_per_tetrahedron = 4
intertwiner_dim = 2
vertex_tetrahedra = 5
pairwise_links = sp.binomial(vertex_tetrahedra, 2)

# Report skeletons.
angles = sp.symbols("theta1:5", real=True)
areas = sp.symbols("A1:5", real=True)
deficit = 2 * sp.pi - sum(angles)
regge_action = sp.simplify(sum(a_i * th_i for a_i, th_i in zip(areas, angles)))

print("SU(2) chart U =")
print(U)
print("U†U =")
print(sp.simplify(UU))
print("sphere factor r² =", r2)
print()
print("intertwiner support length =", len(support))
print("<0I|0I> =", norm0)
print("<1I_raw|1I_raw> =", norm1raw)
print("<0I|1I_raw> =", orth)
print()
print("qubits per tetrahedron =", qubits_per_tetrahedron)
print("intertwiner dimension =", intertwiner_dim)
print("tetrahedra per vertex =", vertex_tetrahedra)
print("pairwise links =", pairwise_links)
print("Regge deficit angle skeleton =", deficit)
print("Regge action skeleton =", regge_action)

assert sp.simplify(UU - r2 * sp.eye(2)) == sp.zeros(2)
assert len(support) == 6
assert norm0 == 1
assert norm1raw == 3
assert orth == 0
assert qubits_per_tetrahedron == 4
assert intertwiner_dim == 2
assert vertex_tetrahedra == 5
assert pairwise_links == 10

print("Bashore LQG report extraction audit passed")
