#!/usr/bin/env python3
"""SymPy audit for the finite Cuntz/Tomita--Takesaki chiral shadow."""
import sympy as sp

c = sp.Rational(5, 4)
s = sp.Rational(3, 4)
I = sp.eye(2)
Pp = sp.Matrix([[1, 0], [0, 0]])
Pm = sp.Matrix([[0, 0], [0, 1]])
eta = Pp - Pm
L = c * I - s * eta
R = c * I + s * eta

x11, x12, x21, x22 = sp.symbols("x11 x12 x21 x22")
X = sp.Matrix([[x11, x12], [x21, x22]])

assert Pp + Pm == I
assert Pp * Pp == Pp
assert Pm * Pm == Pm
assert Pp * Pm == sp.zeros(2)
assert Pm * Pp == sp.zeros(2)
assert eta * eta == I
assert c**2 - s**2 == 1
assert L * R == I
assert R * L == I

Delta = sp.simplify(L * X * R)
J = lambda Y: sp.simplify(L * Y.T * R)
S = sp.simplify(J(Delta))
assert S == X.T

Ep, Em = sp.symbols("Ep Em")
mu = (Ep + Em) / 2
gap = (Ep - Em) / 2
K = Ep * Pp + Em * Pm
assert sp.simplify(K - (mu * I + gap * eta)) == sp.zeros(2)

print("CUNTZ_TOMITA_TAKESAKI_SYMPY_AUDIT_OK")
