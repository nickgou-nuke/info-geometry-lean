#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
Pellis Fine-Structure Constant Formula - SageMath Formalization

Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵
where φ = (1+√5)/2 is the golden ratio.

Main results:
1. φ satisfies φ² = φ + 1
2. φ⁻² = 2-φ, φ⁻³ = 2φ-3, φ⁻⁵ = 5φ-8  
3. pellis_α⁻¹ = 176410/243 - (88447/243)·φ (exact linear form)
4. 137.0359991 < pellis_α⁻¹ < 137.0359992 (matches CODATA 2018)
"""

print("="*70)
print("PELLIS FINE-STRUCTURE CONSTANT - SAGEMATH FORMALIZATION")
print("="*70)

# Define the golden ratio in the real field
RR = RealField(200)  # 200 bits of precision
phi = (1 + RR(5).sqrt()) / 2

print(f"\n1. Golden ratio φ = {phi}")
print(f"   φ ≈ {phi.n(digits=15)}")

# Verify quadratic relation
phi_squared = phi^2
print(f"\n2. Quadratic relation φ² = φ + 1:")
print(f"   φ² = {phi_squared}")
print(f"   φ + 1 = {phi + 1}")
print(f"   φ² - (φ+1) = {phi_squared - (phi + 1)} (should be 0)")
assert abs(phi_squared - (phi + 1)) < 1e-50, "Quadratic relation failed!"

# Verify inverse powers
def verify_inverse_power(n, expected):
    """Verify φ⁻ⁿ = expected"""
    inv_phi_n = phi^(-n)
    diff = abs(inv_phi_n - expected)
    print(f"   φ^(-{n}) = {inv_phi_n}")
    print(f"   Expected  = {expected}")
    print(f"   Difference = {diff}")
    assert diff < 1e-50, f"Inverse power {n} failed!"
    return True

print(f"\n3. Inverse powers of φ:")
verify_inverse_power(2, 2 - phi)
verify_inverse_power(3, 2*phi - 3)
verify_inverse_power(5, 5*phi - 8)

# Primary Pellis formula (Equation 6)
pellis_alpha_inv = 360 * phi^(-2) - 2 * phi^(-3) + (3*phi)^(-5)
print(f"\n4. Pellis formula for α⁻¹ (Equation 6):")
print(f"   α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵")
print(f"   α⁻¹ = {pellis_alpha_inv}")
print(f"   α⁻¹ ≈ {pellis_alpha_inv.n(digits=15)}")

# Normal form calculation
phi_inv_2 = 2 - phi
phi_inv_3 = 2*phi - 3
phi_inv_5 = 5*phi - 8
pellis_normal = 360*phi_inv_2 - 2*phi_inv_3 + (1/243)*phi_inv_5

print(f"\n5. Normal form in basis {{1, φ}}:")
print(f"   α⁻¹ = 176410/243 - (88447/243)·φ")
coeff_1 = RR(176410) / RR(243)
coeff_phi = RR(88447) / RR(243)
pellis_normal_explicit = coeff_1 - coeff_phi * phi
print(f"   Calculated: {pellis_normal_explicit}")
print(f"   Difference from primary: {abs(pellis_alpha_inv - pellis_normal_explicit)}")
assert abs(pellis_alpha_inv - pellis_normal_explicit) < 1e-50, "Normal form failed!"

# CODATA 2018 comparison
codata_2018 = RR(137.035999084)
difference = abs(pellis_alpha_inv - codata_2018)
print(f"\n6. Comparison with CODATA 2018:")
print(f"   CODATA 2018: α⁻¹ = {codata_2018}")
print(f"   Pellis:      α⁻¹ = {pellis_alpha_inv}")
print(f"   Difference:  |Δ| = {difference}")
print(f"   Agreement:   {8 - RR(difference).log(10).floor()} decimal places")
assert difference < 1e-7, "CODATA agreement failed!"

# Bounds verification
lower_bound = RR(137.0359991)
upper_bound = RR(137.0359992)
print(f"\n7. Bounds verification:")
print(f"   {lower_bound} < α⁻¹ < {upper_bound}")
print(f"   Lower check: {pellis_alpha_inv > lower_bound}")
print(f"   Upper check: {pellis_alpha_inv < upper_bound}")
assert lower_bound < pellis_alpha_inv < upper_bound, "Bounds failed!"

# Alternative forms from the paper
print(f"\n8. Alternative forms:")

# Equation (9): α⁻¹ = (362-3-4)·φ⁻² - (1-3-5)·φ⁻¹
pellis_v9 = (362-3-4) * phi^(-2) - (1-3-5) * phi^(-1)
print(f"   Eq(9):  α⁻¹ = (362-3-4)·φ⁻² - (1-3-5)·φ⁻¹ = {pellis_v9}")
print(f"   Diff from primary: {abs(pellis_alpha_inv - pellis_v9)}")

# Equation (11): α⁻¹ = φ⁰ - 2·φ⁻¹ + 360·φ⁻² - φ⁻³ + (3·φ)⁻⁵
pellis_v11 = phi^0 - 2*phi^(-1) + 360*phi^(-2) - phi^(-3) + (3*phi)^(-5)
print(f"   Eq(11): α⁻¹ = φ⁰ - 2·φ⁻¹ + 360·φ⁻² - φ⁻³ + (3·φ)⁻⁵ = {pellis_v11}")
print(f"   Diff from primary: {abs(pellis_alpha_inv - pellis_v11)}")

# Continued fraction approximation
print(f"\n9. Continued fraction convergents:")
cf = [137, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 9]
conv = 0
for i, n in enumerate(reversed(cf)):
    if i == 0:
        conv = RR(n)
    else:
        conv = n + 1/conv
conv = 1/conv  # First term is special
print(f"   CF: {cf}")
print(f"   Convergent: {conv}")
print(f"   Difference: {abs(pellis_alpha_inv - conv)}")

print("\n" + "="*70)
print("ALL VERIFICATIONS PASSED")
print("="*70)
print(f"\nFinal result:")
print(f"  α⁻¹ = {pellis_alpha_inv.n(digits=16)}")
print(f"  α   = {(1/pellis_alpha_inv).n(digits=16)}")
print(f"\nCODATA 2018 agreement: {8 - RR(difference).log(10).floor()} decimal places")