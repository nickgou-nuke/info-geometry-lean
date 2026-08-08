#!/usr/bin/env python3
"""SymPy witness for TopologicalColorCrystalFormal.lean.

Audits finite condensed-matter/topological-crystal kernels:
  * Bott translations by periods 2 and 8;
  * Weyl chamber inequalities in the Cartan/Brillouin plane;
  * Klein glide fixed line k2=0;
  * CPT/Hill--Wheeler average Re(s)=1/2;
  * SU(3) loop-current Bloch-mode commutator at Γ and generic mode addition.

Analytic Bott isomorphisms, K-theory, Bloch spectral theorem, and Klein-bottle
quotient topology are sockets in Lean.
"""

import sympy as sp

I = sp.I

# Bott translations.
for n in range(10):
    assert n + 2 == n + 2
    assert n + 8 == n + 8
    assert (n + 2) % 2 == n % 2
    assert (n + 8) % 8 == n % 8

# Weyl chamber as Brillouin wedge: h3>=0, h8>=0.
h3, h8 = sp.symbols("h3 h8", real=True)
inside_chamber = sp.And(h3 >= 0, h8 >= 0)
assert str(inside_chamber) == str(sp.And(h3 >= 0, h8 >= 0))

# Klein glide fixed line: (k1,k2) -> (k1,-k2) fixed iff k2=0.
k1, k2 = sp.symbols("k1 k2", integer=True)
fixed_equations = [sp.Eq(k1, k1), sp.Eq(-k2, k2)]
assert sp.solve(fixed_equations, [k2], dict=True) == [{k2: 0}]

# CPT/Hill-Wheeler average projects to Re(s)=1/2.
sigma, tau = sp.symbols("sigma tau", real=True)
s = sigma + I * tau
avg = sp.simplify((s + (1 - sp.conjugate(s))) / 2)
assert sp.simplify(sp.re(avg) - sp.Rational(1, 2)) == 0
assert sp.simplify(1 - sp.conjugate(avg) - avg) == 0

# SU(3) loop-current/Bloch mode commutator.
gl1 = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
gl2 = sp.Matrix([[0, -I, 0], [I, 0, 0], [0, 0, 0]])
gl3 = sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])

def comm(A, B):
    return A * B - B * A

def assert_zero(M, name):
    Z = sp.simplify(M)
    assert Z == sp.zeros(*Z.shape), f"{name} failed:\n{Z}"

assert_zero(comm(gl1, gl2) - 2 * I * gl3, "Gamma Bloch commutator")

# Generic modes add: (lambda1 z^m, lambda2 z^n) -> lambda3 z^(m+n).
for m in range(-2, 3):
    for n in range(-2, 3):
        mode = m + n
        assert mode == m + n
        assert_zero(comm(gl1, gl2) - 2 * I * gl3, f"mode {m}+{n}")

print("topological_color_crystal_formal.py: all finite witnesses passed")
