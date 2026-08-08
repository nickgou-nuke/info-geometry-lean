#!/usr/bin/env python3
"""
SymPy witnesses for proofs/LorentzChiralCuntzBridge.lean.

These are audit witnesses only; Lean remains the proof kernel.
They check the finite 2x2/4x4 algebra used by the Lorentz/chiral/Cuntz bridge:
  * explicit diagonal SL(2,C) group law and determinant 1;
  * determinant preservation by chiral conjugation;
  * Pauli soldering determinant = Minkowski quadratic;
  * Fierz/swap completeness in the chiral basis;
  * Weyl/chiral Lorentz generator commutators.
"""

import sympy as sp

I = sp.I
eta, xi = sp.symbols("eta xi")
E, px, py, pz = sp.symbols("E px py pz")
a, b, c, d = sp.symbols("a b c d")

one2 = sp.eye(2)
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
sigma_plus = sp.Matrix([[0, 1], [0, 0]])
sigma_minus = sp.Matrix([[0, 0], [1, 0]])


def assert_zero(M, name):
    if isinstance(M, sp.MatrixBase):
        Z = M.applyfunc(sp.simplify)
        assert Z == sp.zeros(*M.shape), f"{name} failed:\n{Z}"
    else:
        assert sp.simplify(M) == 0, f"{name} failed: {sp.simplify(M)}"


# Explicit diagonal SL(2,C) one-parameter subgroup.
D_eta = sp.diag(sp.exp(eta), sp.exp(-eta))
D_xi = sp.diag(sp.exp(xi), sp.exp(-xi))
D_sum = sp.diag(sp.exp(eta + xi), sp.exp(-(eta + xi)))
assert_zero(D_eta.det() - 1, "det D_eta = 1")
assert_zero(D_eta * D_xi - D_sum, "D_eta D_xi = D_{eta+xi}")

# Generic SL(2,C) determinant preservation under X ↦ g X g^{-1}.
g = sp.Matrix([[a, b], [c, d]])
X = sp.Matrix(sp.symbols("x00 x01 x10 x11")).reshape(2, 2)
# impose det(g)=1 by substituting d=(1+b*c)/a for an invertible chart
chart = {d: (1 + b * c) / a}
g_chart = g.subs(chart)
conjX = sp.simplify(g_chart * X * g_chart.inv())
assert_zero(sp.factor(conjX.det() - X.det()), "det(g X g^-1) = det X on SL2 chart")

# Pauli soldering determinant.
P = sp.Matrix([[E + pz, px - I * py], [px + I * py, E - pz]])
mink = E**2 - px**2 - py**2 - pz**2
assert_zero(sp.expand(P.det() - mink), "det Pauli(P) = Minkowski square")

# Chiral Fierz identity: 1/2(I⊗I + σ3⊗σ3) + σ+⊗σ- + σ-⊗σ+ = Swap.
fierz = sp.Rational(1, 2) * (sp.kronecker_product(one2, one2) + sp.kronecker_product(sigma3, sigma3))
fierz += sp.kronecker_product(sigma_plus, sigma_minus) + sp.kronecker_product(sigma_minus, sigma_plus)
swap = sp.zeros(4, 4)
for left in range(2):
    for right in range(2):
        col = 2 * left + right
        row = 2 * right + left
        swap[row, col] = 1
assert_zero(fierz - swap, "chiral Fierz swap identity")

# Weyl/chiral Lorentz generator commutators.
Jx = sp.Rational(1, 2) * sigma1
Jy = sp.Rational(1, 2) * sigma2
Jz = sp.Rational(1, 2) * sigma3
Kx = I * Jx
Ky = I * Jy
Kz = I * Jz
comm = lambda A, B: A * B - B * A
assert_zero(comm(Jx, Jy) - I * Jz, "[Jx,Jy]=iJz")
assert_zero(comm(Jx, Ky) - I * Kz, "[Jx,Ky]=iKz")
assert_zero(comm(Kx, Ky) - (-I) * Jz, "[Kx,Ky]=-iJz")

print("lorentz_chiral_cuntz_bridge.py: all SymPy witnesses passed")
