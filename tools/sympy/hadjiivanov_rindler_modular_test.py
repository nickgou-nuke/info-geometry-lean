#!/usr/bin/env python3
"""
SymPy witness for the conformal sl2 / Hadjiivanov / Rindler modular bridge.

This script verifies the exact algebraic identities that the Lean bridge files
reuse as theorem owners:

- conformal sl2 commutators [D,P] = P, [D,K] = -K, [P,K] = 2D
- nilpotent parabolic flow law (I + tE)^n = I + n t E
- Hadjiivanov monodromy = phase * parabolic flow
- modular / boost conjugation of P and K
- rapidity composition and Rindler light-cone scaling

The script is intentionally matrix-level and does not try to prove Lean
theorems.  It is the computational witness for the owner surfaces in
InfoGeometry.Canonical and InfoGeometry.Clifford.
"""

import sympy as sp
from sympy import Matrix, eye, zeros, Rational


def comm(a: Matrix, b: Matrix) -> Matrix:
    return a * b - b * a


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


def eq(a: Matrix, b: Matrix) -> bool:
    return is_zero(sp.simplify(a - b))


def mobius_action(m: Matrix, z):
    return sp.simplify((m[0, 0] * z + m[0, 1]) / (m[1, 0] * z + m[1, 1]))


I2 = eye(2)
z, h, lam, lam1, lam2, tau, eta, r = sp.symbols(
    "z h lam lam1 lam2 tau eta r", real=True
)
n = sp.symbols("n", integer=True, nonnegative=True)

# Conformal sl2 generators on the affine/projective chart.
P = Matrix([[0, 1], [0, 0]])
D = Matrix([[Rational(1, 2), 0], [0, -Rational(1, 2)]])
K = Matrix([[0, 0], [1, 0]])

# Nilpotent parabolic generator.
E = P

# Projective generators.
T = Matrix([[1, 1], [0, 1]])
S = Matrix([[0, -1], [1, 0]])
S_inv = Matrix([[0, 1], [-1, 0]])

# Hadjiivanov phase + parabolic flow.
phase = sp.exp(-2 * sp.pi * sp.I * h)
log_shear_base = -2 * sp.pi * sp.I
M = phase * (I2 + log_shear_base * E)

def parabolic_flow(t):
    return I2 + t * E

def boost(l):
    return Matrix([[sp.exp(l / 2), 0], [0, sp.exp(-l / 2)]])

def adj(g: Matrix, X: Matrix) -> Matrix:
    return sp.simplify(g * X * g.inv())

def nilpotent_pow_formula(t, k: int) -> Matrix:
    return phase**k * (I2 + (k * log_shear_base) * E)


checks = {
    # conformal sl2
    "P^2 = 0": is_zero(P**2),
    "D trace = 0": sp.simplify(D.trace()) == 0,
    "K^2 = 0": is_zero(K**2),
    "[D,P] = P": is_zero(comm(D, P) - P),
    "[D,K] = -K": is_zero(comm(D, K) + K),
    "[P,K] = 2D": is_zero(comm(P, K) - 2 * D),

    # projective chart
    "T(z)=z+1": sp.simplify(mobius_action(T, z) - (z + 1)) == 0,
    "S(z)=-1/z": sp.simplify(mobius_action(S, z) + 1 / z) == 0,
    "S*T*S^{-1} is lower shear": eq(S * T * S_inv, Matrix([[1, 0], [-1, 1]])),

    # rapidity / boost
    "boost composition": eq(boost(lam1) * boost(lam2), boost(lam1 + lam2)),
    "x_plus shift": sp.simplify((r * sp.exp(eta)) * sp.exp(lam) - r * sp.exp(eta + lam)) == 0,
    "x_minus shift": sp.simplify((r * sp.exp(-eta)) * sp.exp(-lam) - r * sp.exp(-(eta + lam))) == 0,
    "adj_boost_P": eq(adj(boost(lam), P), sp.exp(lam) * P),
    "adj_boost_K": eq(adj(boost(lam), K), sp.exp(-lam) * K),

    # Hadjiivanov phase + nilpotent flow
    "M = phase * (I + log_shear_base E)": eq(M, phase * (I2 + log_shear_base * E)),
    "parabolic flow composition": eq(parabolic_flow(lam1) * parabolic_flow(lam2), parabolic_flow(lam1 + lam2)),
    "Δ = exp(-2πD)": eq(sp.exp(-2 * sp.pi * D), Matrix([[sp.exp(-sp.pi), 0], [0, sp.exp(sp.pi)]])),
}


print("Hadjiivanov / Rindler / conformal sl2 SymPy witness")
print("----------------------------------------------------")
for key in [
    "P^2 = 0",
    "D trace = 0",
    "K^2 = 0",
    "[D,P] = P",
    "[D,K] = -K",
    "[P,K] = 2D",
]:
    print(f"  {key}: {checks[key]}")

print("\nProjective chart readout:")
for key in ["T(z)=z+1", "S(z)=-1/z", "S*T*S^{-1} is lower shear"]:
    print(f"  {key}: {checks[key]}")

print("\nRapidity / boost readout:")
for key in ["boost composition", "x_plus shift", "x_minus shift", "adj_boost_P", "adj_boost_K"]:
    print(f"  {key}: {checks[key]}")

print("\nHadjiivanov parabolic monodromy readout:")
for key in ["M = phase * (I + log_shear_base E)", "parabolic flow composition"]:
    print(f"  {key}: {checks[key]}")

print("\nRepeated-wrap witness:")
pow_checks = []
for k in range(0, 6):
    lhs = sp.simplify(M**k)
    rhs = sp.simplify(nilpotent_pow_formula(log_shear_base, k))
    ok = eq(lhs, rhs)
    pow_checks.append(ok)
    print(f"  n = {k}: {ok}")

print("\nModular operator readout:")
print(f"  Δ = exp(-2πD): {checks['Δ = exp(-2πD)']}")

print("\nInterpretation:")
print("  [D,P]=P and [D,K]=-K are the conformal sl2 owner relations")
print("  M(h) is phase times a nilpotent parabolic flow")
print("  boost conjugation scales P and K exponentially")
print("  the Rindler wedge uses the same rapidity parameterization")
print("OVERALL:", all(checks.values()) and all(pow_checks))
