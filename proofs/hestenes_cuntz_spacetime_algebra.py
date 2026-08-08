#!/usr/bin/env python3
"""
SymPy witnesses for proofs/HestenesCuntzSpacetimeAlgebra.lean.

Audit-only finite witnesses. Lean is the proof kernel.
Checks:
  * Pauli paravector soldering and coordinate dual readout;
  * determinant = Minkowski norm;
  * polarization pairing formula;
  * Pauli/Clifford spatial anticommutation spine;
  * chiral Fierz/swap completeness;
  * Lorentz determinant covariance on an SL(2,C) chart.
"""

import sympy as sp

I = sp.I
E, px, py, pz = sp.symbols("E px py pz")
F, qx, qy, qz = sp.symbols("F qx qy qz")
a, b, c, d = sp.symbols("a b c d")

sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
sigma_plus = sp.Matrix([[0, 1], [0, 0]])
sigma_minus = sp.Matrix([[0, 0], [1, 0]])
one2 = sp.eye(2)
zero2 = sp.zeros(2)


def assert_zero(expr, name):
    if isinstance(expr, sp.MatrixBase):
        z = expr.applyfunc(sp.simplify)
        assert z == sp.zeros(*expr.shape), f"{name} failed:\n{z}"
    else:
        assert sp.simplify(expr) == 0, f"{name} failed: {sp.simplify(expr)}"


def paravector(t, x, y, z):
    return sp.Matrix([[t + z, x - I * y], [x + I * y, t - z]])


def recover(A):
    t = sp.Rational(1, 2) * sp.trace(A)
    x = sp.Rational(1, 2) * sp.trace(A * sigma1)
    y = sp.Rational(1, 2) * sp.trace(A * sigma2)
    z = sp.Rational(1, 2) * sp.trace(A * sigma3)
    return tuple(map(sp.simplify, (t, x, y, z)))

P = paravector(E, px, py, pz)
Q = paravector(F, qx, qy, qz)

# Coordinate duals recover soldered four-vector components.
assert recover(P) == (E, px, py, pz)

# Determinant gives the Hestenes/Minkowski paravector norm.
minkP = E**2 - px**2 - py**2 - pz**2
assert_zero(sp.expand(P.det() - minkP), "det paravector = Minkowski norm")

# Polarization gives the Minkowski pairing.
minkQ = F**2 - qx**2 - qy**2 - qz**2
PQ = paravector(E + F, px + qx, py + qy, pz + qz)
pair = sp.Rational(1, 2) * (PQ.det() - minkP - minkQ)
assert_zero(sp.expand(pair - (E * F - px * qx - py * qy - pz * qz)), "polarized pairing")

# Pauli/Clifford spatial spine.
assert_zero(sigma1 * sigma1 - one2, "sigma1^2")
assert_zero(sigma2 * sigma2 - one2, "sigma2^2")
assert_zero(sigma3 * sigma3 - one2, "sigma3^2")
assert_zero(sigma1 * sigma2 + sigma2 * sigma1, "{sigma1,sigma2}=0")
assert_zero(sigma1 * sigma3 + sigma3 * sigma1, "{sigma1,sigma3}=0")
assert_zero(sigma2 * sigma3 + sigma3 * sigma2, "{sigma2,sigma3}=0")

# Fierz completeness / swap identity.
fierz = sp.Rational(1, 2) * (sp.kronecker_product(one2, one2) + sp.kronecker_product(sigma3, sigma3))
fierz += sp.kronecker_product(sigma_plus, sigma_minus) + sp.kronecker_product(sigma_minus, sigma_plus)
swap = sp.zeros(4, 4)
for left in range(2):
    for right in range(2):
        col = 2 * left + right
        row = 2 * right + left
        swap[row, col] = 1
assert_zero(fierz - swap, "Fierz swap completeness")

# Lorentz covariance as determinant preservation under SL2 conjugation on a chart det(g)=1.
g = sp.Matrix([[a, b], [c, d]])
g_chart = g.subs({d: (1 + b * c) / a})
transformed = sp.simplify(g_chart * P * g_chart.inv())
assert_zero(sp.factor(transformed.det() - P.det()), "SL2 conjugation preserves paravector determinant")

print("hestenes_cuntz_spacetime_algebra.py: all SymPy witnesses passed")
