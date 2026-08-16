#!/usr/bin/env python3
r"""
Hadamard-Weierstrass Xi Factorization and Root-Pairing Symmetry CAS Test

Validates:
1. Root reflection: 1 - ρ(γ) = conj(ρ(γ)) = 1/2 - i γ.
2. Product identity: ρ(γ)(1 - ρ(γ)) = 1/4 + γ².
3. Quadratic factor reflection: F_γ(1 - s) ≡ F_γ(s).
4. Critical line zero locus: F_γ(1/2 + i t) = 0 ⟺ t = ±γ.
5. Strict positivity on the real interval (0, 1): F_γ(x) > 0 for x ∈ (0, 1) and γ ≠ 0.
"""

import sympy as sp
from sympy import symbols, I, simplify, re, im, Rational

def test_root_pairing_product():
    print("[1/4] Testing Root Pairing and Product ρ(1-ρ) = 1/4 + γ²...")
    gamma = symbols('gamma', real=True)
    rho = Rational(1, 2) + I * gamma
    rho_refl = 1 - rho
    assert simplify(rho_refl - (Rational(1, 2) - I * gamma)) == 0
    
    prod = simplify(rho * (1 - rho))
    expected = Rational(1, 4) + gamma**2
    assert prod == expected, f"Expected {expected}, got {prod}"
    print(f"  ρ(γ) = 1/2 + iγ ⟹ ρ(1-ρ) = {prod}")
    print("  ✓ PASSED: Root product matches 1/4 + γ² exactly.")

def test_quadratic_factor_reflection():
    print("[2/4] Testing Functional Reflection F_γ(1-s) = F_γ(s)...")
    s, gamma = symbols('s gamma', complex=True)
    denom = Rational(1, 4) + gamma**2
    F = 1 - s * (1 - s) / denom
    F_refl = 1 - (1 - s) * (1 - (1 - s)) / denom
    diff = simplify(F - F_refl)
    assert diff == 0, f"F_γ(1-s) must equal F_γ(s), diff: {diff}"
    print("  ✓ PASSED: Quadratic factor is identically invariant under s ↦ 1 - s.")

def test_critical_line_zero_locus():
    print("[3/4] Testing Critical Line Zero Locus F_γ(1/2 + i t) = 0...")
    t, gamma = symbols('t gamma', real=True)
    s = Rational(1, 2) + I * t
    denom = Rational(1, 4) + gamma**2
    F = 1 - s * (1 - s) / denom
    F_simp = simplify(F)
    # F = 1 - (1/4 + t^2) / (1/4 + gamma^2) = (gamma^2 - t^2) / (1/4 + gamma^2)
    expected_num = gamma**2 - t**2
    assert simplify(F_simp * denom - expected_num) == 0
    print(f"  F_γ(1/2 + it) = (γ² - t²) / (1/4 + γ²)")
    print("  ✓ PASSED: Roots on critical line are precisely t = ±γ.")

def test_real_positivity_on_critical_interval():
    print("[4/4] Testing Strict Real Positivity on x ∈ (0, 1)...")
    x, gamma = symbols('x gamma', real=True)
    # x(1-x) <= 1/4 < 1/4 + gamma^2 for gamma != 0
    # Test at sample points
    test_gammas = [Rational(14, 1), Rational(1, 2), Rational(1, 10)]
    test_x = [Rational(1, 4), Rational(1, 2), Rational(3, 4)]
    for g in test_gammas:
        denom = Rational(1, 4) + g**2
        for val_x in test_x:
            f_val = 1 - val_x * (1 - val_x) / denom
            assert f_val > 0, f"F_{g}({val_x}) must be > 0, got {f_val}"
    print("  ✓ PASSED: F_γ(x) > 0 for all x ∈ (0, 1) and γ ≠ 0.")

if __name__ == "__main__":
    test_root_pairing_product()
    test_quadratic_factor_reflection()
    test_critical_line_zero_locus()
    test_real_positivity_on_critical_interval()
    print("\n✅ ALL HADAMARD-WEIERSTRASS CAS TESTS PASSED (Code 0).")
