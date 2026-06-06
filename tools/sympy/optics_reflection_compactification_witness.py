#!/usr/bin/env python3
"""
SymPy witness for the optics / reflection / compactification corridor.

This script checks the finite operator identities that mirror the Lean owner
surfaces for:

- Jones s/p projectors and diagonal Jones decomposition,
- Brewster collapse (p-channel vanishes),
- BdG / Andreev reflection as a 90-degree rotation with square `-I`,
- Möbius / Poincare inversion and dilation-sign flip,
- upper-to-lower shear conjugation under inversion.

The goal is to witness the matrix algebra explicitly, not to replace Lean.
"""

import sympy as sp
from sympy import Matrix, eye, zeros, Rational


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


def eq(a: Matrix, b: Matrix) -> bool:
    return is_zero(sp.simplify(a - b))


def mobius_action(m: Matrix, z):
    return sp.simplify((m[0, 0] * z + m[0, 1]) / (m[1, 0] * z + m[1, 1]))


print("Optics / reflection / compactification SymPy witness")
print("-----------------------------------------------------")

# ---------------------------------------------------------------------
# 1. Jones/Fresnel two-channel packet
# ---------------------------------------------------------------------
Ps = Matrix([[1, 0], [0, 0]])
Pp = Matrix([[0, 0], [0, 1]])
r_s, r_p = sp.symbols("r_s r_p")
J = Matrix([[r_s, 0], [0, r_p]])

jones_checks = {
    "Ps^2 = Ps": eq(Ps * Ps, Ps),
    "Pp^2 = Pp": eq(Pp * Pp, Pp),
    "Ps Pp = 0": eq(Ps * Pp, zeros(2)),
    "Pp Ps = 0": eq(Pp * Ps, zeros(2)),
    "Ps + Pp = I": eq(Ps + Pp, eye(2)),
    "J = r_s Ps + r_p Pp": eq(J, r_s * Ps + r_p * Pp),
    "Brewster collapse p=0": eq(Matrix([[r_s, 0], [0, 0]]), r_s * Ps),
}

print("\nJones / Fresnel packet:")
for key in [
    "Ps^2 = Ps",
    "Pp^2 = Pp",
    "Ps Pp = 0",
    "Pp Ps = 0",
    "Ps + Pp = I",
    "J = r_s Ps + r_p Pp",
    "Brewster collapse p=0",
]:
    print(f"  {key}: {jones_checks[key]}")

v_s = Matrix([sp.symbols("a"), 0])
v_p = Matrix([0, sp.symbols("b")])
brewster_survival = eq(Matrix([[r_s, 0], [0, 0]]) * v_s, r_s * v_s)
brewster_kill_p = eq(Matrix([[r_s, 0], [0, 0]]) * v_p, zeros(2, 1))

print("  Brewster preserves s-input: ", brewster_survival)
print("  Brewster kills p-input:      ", brewster_kill_p)

# ---------------------------------------------------------------------
# 2. Andreev finite BdG reflection atom
# ---------------------------------------------------------------------
e, h = sp.symbols("e h", real=True)
A = Matrix([[0, -1], [1, 0]])
psi = Matrix([e, h])

andreev_checks = {
    "A^2 = -I": eq(A * A, -eye(2)),
    "A^4 = I": eq(A ** 4, eye(2)),
    "A(e,h) = (-h,e)": eq(A * psi, Matrix([-h, e])),
    "A^2(e,h) = -(e,h)": eq(A * (A * psi), -psi),
}

print("\nAndreev / BdG packet:")
for key in ["A^2 = -I", "A^4 = I", "A(e,h) = (-h,e)", "A^2(e,h) = -(e,h)"]:
    print(f"  {key}: {andreev_checks[key]}")

# ---------------------------------------------------------------------
# 3. Poincare / Möbius compactification packet
# ---------------------------------------------------------------------
z, lam = sp.symbols("z lam", real=True)
P = Matrix([[0, 1], [0, 0]])
D = Matrix([[Rational(1, 2), 0], [0, -Rational(1, 2)]])
K = Matrix([[0, 0], [1, 0]])
S = Matrix([[0, -1], [1, 0]])
T = Matrix([[1, 1], [0, 1]])
S_inv = Matrix([[0, 1], [-1, 0]])

def adj(g: Matrix, X: Matrix) -> Matrix:
    return sp.simplify(g * X * g.inv())

compact_checks = {
    "S^2 = -I": eq(S * S, -eye(2)),
    "S P S^-1 = -K": eq(adj(S, P), -K),
    "S D S^-1 = -D": eq(adj(S, D), -D),
    "S K S^-1 = -P": eq(adj(S, K), -P),
    "S exp(lam D) S^-1 = exp(-lam D)":
        eq(sp.simplify(S * (lam * D).exp() * S_inv), sp.simplify((-lam * D).exp())),
    "S T S^-1 = lower shear": eq(S * T * S_inv, Matrix([[1, 0], [-1, 1]])),
}

print("\nPoincare / Möbius compactification packet:")
for key in [
    "S^2 = -I",
    "S P S^-1 = -K",
    "S D S^-1 = -D",
    "S K S^-1 = -P",
    "S exp(lam D) S^-1 = exp(-lam D)",
    "S T S^-1 = lower shear",
]:
    print(f"  {key}: {compact_checks[key]}")

print("  S(z) =", mobius_action(S, z))
print("  T(z) =", mobius_action(T, z))

# ---------------------------------------------------------------------
# 4. Combined interpretation
# ---------------------------------------------------------------------
print("\nInterpretation:")
print("  Jones projectors split the finite s/p optical carrier.")
print("  Brewster collapse is the vanishing of the p-channel.")
print("  Andreev reflection is a square-minus-one involutive rotation.")
print("  Möbius inversion swaps the upper/lower shear and flips dilation sign.")
print("OVERALL:", all(jones_checks.values()) and all(andreev_checks.values()) and all(compact_checks.values()))
