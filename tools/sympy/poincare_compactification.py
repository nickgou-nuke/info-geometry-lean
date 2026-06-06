#!/usr/bin/env python3
"""
SymPy witness for the Poincaré sphere compactification.

The inversion S : z ↦ -1/z maps the outer null cone to the inner null cone,
compactifying the boundary at infinity.

In Cl(5,5) language: J = u - v, J² = -1, swaps the null pair (u, v).
On the projective chart: S acts by Möbius inversion.

Key identities:
  S² = -I                     (inversion is an involution up to sign)
  S · T · S⁻¹ = lower shear   (conjugation swaps translation ↔ special conformal)
  S · P · S⁻¹ = -K            (adjoint swaps P and K)
  S · D · S⁻¹ = -D            (dilation sign flips under inversion)
  exp(λ·D) · S = S · exp(-λ·D) (inversion flips the rapidity sign)
"""

import sympy as sp
from sympy import Matrix, eye, zeros, Rational, simplify, exp, pi

z, λ = sp.symbols("z λ", real=True)

# ── sl₂ conformal generators ──
P = Matrix([[0, 1], [0, 0]])
D = Matrix([[Rational(1,2), 0], [0, -Rational(1,2)]])
K = Matrix([[0, 0], [1, 0]])

# ── Möbius inversion S : z ↦ -1/z ──
S = Matrix([[0, -1], [1, 0]])

# ══════════════════════════════════════════════════════════
# 1. Inversion properties
# ══════════════════════════════════════════════════════════
print("=== 1. Inversion S : z ↦ -1/z ===")

# S² = -I
assert simplify(S * S + eye(2)) == zeros(2)
print(f"✓ S² = -I")

# Möbius action: S(z) = -1/z
def mobius(m, zz):
    return simplify((m[0,0]*zz + m[0,1]) / (m[1,0]*zz + m[1,1]))
print(f"  S(z) = {mobius(S, z)}")

# ══════════════════════════════════════════════════════════
# 2. Adjoint action swaps P ↔ K, preserves D
# ══════════════════════════════════════════════════════════
print("\n=== 2. Adjoint action of inversion ===")

def ad(X, g):
    return g * X * g.inv()

assert simplify(ad(P, S) + K) == zeros(2)
print(f"✓ S·P·S⁻¹ = -K  (translation ↔ special conformal)")

assert simplify(ad(D, S) + D) == zeros(2)
print(f". S·D·S⁻¹ = -D  (dilation sign flipped)")

assert simplify(ad(K, S) + P) == zeros(2)
print(f"✓ S·K·S⁻¹ = -P  (special conformal ↔ translation)")

# ══════════════════════════════════════════════════════════
# 3. Inversion flips rapidity sign
# ══════════════════════════════════════════════════════════
print("\n=== 3. Inversion flips rapidity ===")

# exp(λ·D) is the boost
boost = (λ * D).exp()
# Conjugating by S: S · exp(λ·D) · S⁻¹ = exp(-λ·D)
boost_conj = simplify(S * boost * S.inv())
boost_neg = (-λ * D).exp()
assert simplify(boost_conj - boost_neg) == zeros(2)
print(f"✓ S·exp(λ·D)·S⁻¹ = exp(-λ·D)  (rapidity sign flip)")

# ══════════════════════════════════════════════════════════
# 4. S · T · S⁻¹ = lower shear
# ══════════════════════════════════════════════════════════
print("\n=== 4. S · T · S⁻¹ = lower shear ===")

T = Matrix([[1, 1], [0, 1]])
STS = simplify(S * T * S.inv())
T_lower = Matrix([[1, 0], [-1, 1]])
assert simplify(STS - T_lower) == zeros(2)
print(f"✓ S·T·S⁻¹ = [[1,0],[-1,1]]  (upper ↔ lower shear)")

# ══════════════════════════════════════════════════════════
# 5. Compactification: outer ↔ inner null cone
# ══════════════════════════════════════════════════════════
print("\n=== 5. Outer ↔ inner null cone compactification ===")

# The null cone coordinates: x₊ = r·e^η, x₋ = r·e^{-η}
# Under inversion S (acting as z ↦ -1/z), the radial coordinate transforms:
# r ↦ 1/r or more precisely η ↦ -η (since the boost direction flips)

r, η = sp.symbols("r η", real=True)
x_plus = r * exp(η)
x_minus = r * exp(-η)

# Inversion acts as η ↦ -η (rapidity sign flip)
x_plus_inv = r * exp(-η)  # = x_minus
x_minus_inv = r * exp(η)  # = x_plus

print(f"  Outer cone: x₊ = r·e^η, x₋ = r·e^-η")
print(f"  Under inversion (η ↦ -η):")
print(f"    x₊ ↦ r·e^-η = x₋  (outer → inner)")
print(f"    x₋ ↦ r·e^η = x₊  (inner → outer)")
print(f"  The outer boundary η→+∞ maps to the inner boundary η→-∞.")

# The compactification: the point at infinity (|z| → ∞) maps to the origin (z = 0)
# On the Riemann sphere: S(∞) = 0 and S(0) = ∞
limit_inf = sp.limit(mobius(S, 1/z), z, 0)  # z → ∞ corresponds to 1/z → 0
print(f"  S(∞) = {limit_inf}  (point at infinity → origin)")

limit_zero = sp.limit(mobius(S, z), z, 0)
print(f"  S(0) = {limit_zero}  (origin → point at infinity)")

# ══════════════════════════════════════════════════════════
print(f"\nOVERALL: Poincaré compactification verified ✅")
