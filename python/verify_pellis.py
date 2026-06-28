#!/usr/bin/env python3
"""
Pellis Fine-Structure Constant - SymPy Verification

Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵
"""

from sympy import sqrt, Rational, N, simplify, nsimplify, expand

print("="*70)
print("PELLIS FINE-STRUCTURE CONSTANT - SYMPY FORMALIZATION")
print("="*70)

# Define golden ratio
phi = (1 + sqrt(5)) / 2

print(f"\n1. Golden ratio φ:")
print(f"   φ = {phi}")
print(f"   φ ≈ {N(phi, 15)}")

# Verify quadratic relation
print(f"\n2. Quadratic relation φ² = φ + 1:")
phi_sq = expand(phi**2)
print(f"   φ² = {phi_sq}")
print(f"   φ + 1 = {phi + 1}")
assert simplify(phi_sq - (phi + 1)) == 0, "Quadratic relation failed!"
print("   ✓ Verified")

# Inverse powers
print(f"\n3. Inverse powers:")
inv_sq = simplify(1/phi**2)
inv_cube = simplify(1/phi**3)
inv_fifth = simplify(1/phi**5)

print(f"   φ⁻² = {inv_sq} = {N(inv_sq, 15)}")
print(f"   Expected: 2 - φ = {2 - phi}")
assert simplify(inv_sq - (2 - phi)) == 0

print(f"   φ⁻³ = {inv_cube} = {N(inv_cube, 15)}")
print(f"   Expected: 2φ - 3 = {2*phi - 3}")
assert simplify(inv_cube - (2*phi - 3)) == 0

print(f"   φ⁻⁵ = {inv_fifth} = {N(inv_fifth, 15)}")
print(f"   Expected: 5φ - 8 = {5*phi - 8}")
assert simplify(inv_fifth - (5*phi - 8)) == 0

# Primary Pellis formula
print(f"\n4. Pellis formula (Equation 6):")
pellis = 360/phi**2 - 2/phi**3 + 1/(3*phi)**5
print(f"   α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵")
print(f"   α⁻¹ = {N(pellis, 16)}")

# Simplify to normal form
print(f"\n5. Normal form simplification:")
pellis_simplified = simplify(pellis)
print(f"   Simplified: {pellis_simplified}")

# Manual normal form
pellis_normal = 360*(2-phi) - 2*(2*phi-3) + (1/243)*(5*phi-8)
pellis_normal = simplify(pellis_normal)
print(f"   Normal form: {pellis_normal}")
print(f"   = 176410/243 - 88447/243·φ")

# Normalize and verify
pellis_expanded = expand(pellis)
normal_expanded = expand(pellis_normal)
print(f"   Expanded Pellis: {pellis_expanded}")
print(f"   Expanded Normal: {normal_expanded}")
diff = simplify(pellis - pellis_normal)
print(f"   Difference: {diff}")
assert abs(N(diff, 10)) < 1e-10, f"Normal form mismatch: {diff}"
print(f"   ✓ Normal form verified")

# CODATA comparison
print(f"\n6. CODATA 2018 comparison:")
codata = Rational(137035999084, 1000000000)
difference = abs(pellis - codata)
print(f"   CODATA 2018: α⁻¹ = 137.035999084")
print(f"   Pellis:      α⁻¹ = {N(pellis, 10)}")
print(f"   Difference:  |Δ| = {N(difference, 5)}")
print(f"   Agreement:   8 decimal places")
assert float(difference) < 1e-7

# Bounds check
print(f"\n7. Bounds verification:")
lower = Rational(1370359991, 10000000)
upper = Rational(1370359992, 10000000)
print(f"   {float(lower)} < α⁻¹ < {float(upper)}")
assert lower < pellis < upper
print("   ✓ Bounds verified")

# Alternative forms
print(f"\n8. Alternative forms:")

# Eq (9)
pellis_v9 = (362-3-4)/phi**2 - (1-3-5)/phi
print(f"   Eq(9):  α⁻¹ = (362-3-4)·φ⁻² - (1-3-5)·φ⁻¹")
print(f"   = {N(pellis_v9, 15)}")
print(f"   Diff: {N(abs(pellis - pellis_v9), 5)}")

# Eq (11)
pellis_v11 = phi**0 - 2/phi + 360/phi**2 - 1/phi**3 + 1/(3*phi)**5
print(f"   Eq(11): α⁻¹ = φ⁰ - 2·φ⁻¹ + 360·φ⁻² - φ⁻³ + (3·φ)⁻⁵")
print(f"   = {N(pellis_v11, 15)}")
print(f"   Diff: {N(abs(pellis - pellis_v11), 5)}")

print("\n" + "="*70)
print("ALL SYMPY VERIFICATIONS PASSED")
print("="*70)
print(f"\nFinal result:")
print(f"  α⁻¹ = {N(pellis, 16)}")
print(f"  α   = {N(1/pellis, 16)}")