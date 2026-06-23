#!/usr/bin/env python3
"""
SymPy Verification: Bost-Connes Liouville-Modular Flow Commutation

This script symbolically verifies that the Liouville grading operator Γ
(prime factor parity (-1)^Ω(n)) commutes with the modular flow σ_t.

Theorem: [Γ, σ_t] = 0 for all t ∈ ℝ, n ∈ ℕ⁺

Physical meaning: The Witten index is conserved under thermal time evolution.
"""

import sympy as sp
from sympy import I, exp, log, symbols
from collections import Counter


def omega(n: int) -> int:
    """
    Total number of prime factors of n (with multiplicity).
    
    Examples:
        omega(1) = 0
        omega(2) = 1
        omega(4) = omega(2^2) = 2
        omega(6) = omega(2*3) = 2
        omega(12) = omega(2^2*3) = 3
    """
    if n <= 0:
        raise ValueError("n must be positive")
    if n == 1:
        return 0
    factors = sp.factorint(n)
    return sum(multiplicity for multiplicity in factors.values())


def liouville_grading(n: int) -> int:
    """
    The Liouville grading: Γ(n) = (-1)^Ω(n)
    
    This is the fermion parity operator in the thermofield context.
    """
    return (-1) ** omega(n)


def modular_flow_phase(t, n: int):
    """
    The modular flow phase factor: σ_t(μ_n) = n^{it} · μ_n
    
    Here n^{it} = e^{it·ln(n)} is the phase factor.
    
    Parameters
    ==========
    t : real parameter (time / modular flow parameter)
    n : positive integer (generator index)
    
    Returns
    =======
    sympy expression for n^{it}
    """
    if n <= 0:
        raise ValueError("n must be positive")
    return exp(I * t * log(n))


def verify_commutation_on_basis(t_val=None):
    """
    Verify that Γ and σ_t commute on the basis elements μ_n.
    
    The commutation relation is:
        Γ(σ_t(μ_n)) = σ_t(Γ(μ_n))
    
    Since both operators act diagonally:
        Γ(μ_n) = (-1)^Ω(n) · μ_n
        σ_t(μ_n) = n^{it} · μ_n
    
    The commutation reduces to checking that the scalar factors commute:
        (-1)^Ω(n) · n^{it} = n^{it} · (-1)^Ω(n)
    
    This is trivially true (scalars commute), but we verify it symbolically.
    """
    print("=" * 80)
    print("SYMPY: Liouville-Modular Flow Commutation Verification")
    print("=" * 80)
    
    # Define the time parameter
    t = symbols('t', real=True) if t_val is None else t_val
    
    # Test cases: (n, expected_result)
    test_cases = [
        (1, True),    # Ω(1) = 0, Γ(1) = 1
        (2, True),    # Ω(2) = 1, Γ(2) = -1 (prime)
        (3, True),    # Ω(3) = 1, Γ(3) = -1 (prime)
        (4, True),    # Ω(4) = 2, Γ(4) = 1 (2^2)
        (5, True),    # Ω(5) = 1, Γ(5) = -1 (prime)
        (6, True),    # Ω(6) = 2, Γ(6) = 1 (2*3)
        (8, True),    # Ω(8) = 3, Γ(8) = -1 (2^3)
        (9, True),    # Ω(9) = 2, Γ(9) = 1 (3^2)
        (10, True),   # Ω(10) = 2, Γ(10) = 1 (2*5)
        (12, True),   # Ω(12) = 3, Γ(12) = -1 (2^2*3)
        (30, True),   # Ω(30) = 3, Γ(30) = -1 (2*3*5)
        (100, True),  # Ω(100) = 4, Γ(100) = 1 (2^2*5^2)
    ]
    
    print("\n### 1. Basis Element Verification ###\n")
    all_passed = True
    
    for n, _ in test_cases:
        # Compute both sides of the commutation relation
        gamma_scalar = liouville_grading(n)
        sigma_phase = modular_flow_phase(t, n)
        
        # Left side: Γ(σ_t(μ_n)) = Γ(n^{it} · μ_n) = (-1)^Ω(n) · n^{it} · μ_n
        left_side = gamma_scalar * sigma_phase
        
        # Right side: σ_t(Γ(μ_n)) = σ_t((-1)^Ω(n) · μ_n) = (-1)^Ω(n) · n^{it} · μ_n
        right_side = sigma_phase * gamma_scalar
        
        # Check equality (trivially true for scalars)
        commutes = sp.simplify(left_side - right_side) == 0
        
        if not commutes:
            print(f"❌ FAIL: n={n}, Ω(n)={omega(n)}, Γ(n)={gamma_scalar}")
            print(f"   Left side:  {left_side}")
            print(f"   Right side: {right_side}")
            all_passed = False
        else:
            print(f"✓ n={n:3d}: Ω(n)={omega(n):2d}, Γ(n)={gamma_scalar:+2d}, phase = {n}^{{it}}")
    
    if all_passed:
        print("\n✅ All basis elements pass the commutation check!\n")
    else:
        print("\n❌ Some basis elements failed!\n")
        return False
    
    return True


def verify_multiplicativity():
    """
    Verify that the Liouville grading is completely multiplicative:
        Γ(nm) = Γ(n) · Γ(m)
    
    This follows from: Ω(nm) = Ω(n) + Ω(m) (mod 2)
    
    This property is crucial for the commutation theorem because it ensures
    Γ is a well-defined character on the multiplicative monoid ℕ⁺.
    """
    print("\n" + "=" * 80)
    print("SYMPY: Complete Multiplicativity of Liouville Grading")
    print("=" * 80)
    print("\nVerifying: Γ(nm) = Γ(n) · Γ(m) for various n, m\n")
    
    test_pairs = [
        (2, 3),    # primes
        (4, 9),    # prime powers
        (6, 10),   # composites
        (2, 6),    # prime and composite
        (15, 8),   # 3*5 and 2^3
        (12, 18),  # 2^2*3 and 2*3^2
        (1, 100),  # identity
        (7, 11),   # distinct primes
        (3, 9),    # prime and its power
        (30, 42),  # 2*3*5 and 2*3*7
    ]
    
    all_passed = True
    
    for n, m in test_pairs:
        gamma_n = liouville_grading(n)
        gamma_m = liouville_grading(m)
        gamma_nm = liouville_grading(n * m)
        
        # Check multiplicativity
        is_multiplicative = gamma_nm == gamma_n * gamma_m
        
        if not is_multiplicative:
            print(f"❌ FAIL: Γ({n}*{m}) = {gamma_nm}, but Γ({n})*Γ({m}) = {gamma_n * gamma_m}")
            all_passed = False
        else:
            print(f"✓ Γ({n:2d} * {m:2d}) = Γ({n*m:3d}) = {gamma_nm:+2d} = {gamma_n:+2d} · {gamma_m:+2d}")
    
    if all_passed:
        print("\n✅ Liouville grading is completely multiplicative!\n")
    else:
        print("\n❌ Multiplicativity failed!\n")
        return False
    
    return True


def verify_omega_additivity():
    """
    Verify the additive property of Ω(n):
        Ω(nm) = Ω(n) + Ω(m)
    
    This is the fundamental property that makes Γ multiplicative.
    """
    print("\n" + "=" * 80)
    print("SYMPY: Additivity of the Prime Factor Counting Function Ω(n)")
    print("=" * 80)
    print("\nVerifying: Ω(nm) = Ω(n) + Ω(m)\n")
    
    test_pairs = [
        (2, 3),      # 1 + 1 = 2
        (4, 9),      # 2 + 2 = 4
        (6, 10),     # 2 + 2 = 4
        (12, 18),    # 3 + 3 = 6
        (1, 100),    # 0 + 4 = 4
        (30, 42),    # 3 + 3 = 6
        (64, 27),    # 6 + 3 = 9 (2^6 and 3^3)
        (100, 100),  # 4 + 4 = 8
    ]
    
    all_passed = True
    
    for n, m in test_pairs:
        omega_n = omega(n)
        omega_m = omega(m)
        omega_nm = omega(n * m)
        
        # Check additivity
        is_additive = omega_nm == omega_n + omega_m
        
        if not is_additive:
            print(f"❌ FAIL: Ω({n}*{m}) = {omega_nm}, but Ω({n}) + Ω({m}) = {omega_n + omega_m}")
            all_passed = False
        else:
            print(f"✓ Ω({n:3d}) + Ω({m:3d}) = {omega_n:2d} + {omega_m:2d} = {omega_n + omega_m:2d} = Ω({n*m:4d})")
    
    if all_passed:
        print("\n✅ Ω(n) is perfectly additive!\n")
    else:
        print("\n❌ Additivity failed!\n")
        return False
    
    return True


def verify_phase_cocycle():
    """
    Verify that the modular flow phase factors form a 1-cocycle:
        (nm)^{it} = n^{it} · m^{it}
    
    This ensures σ_t is a homomorphism from ℕ⁺ to the unit circle.
    """
    print("\n" + "=" * 80)
    print("SYMPY: Modular Flow Phase Cocycle Property")
    print("=" * 80)
    print("\nVerifying: (nm)^{{it}} = n^{{it}} · m^{{it}}\n")
    
    t = symbols('t', real=True)
    
    test_pairs = [
        (2, 3),
        (4, 9),
        (6, 10),
        (12, 18),
        (1, 100),
        (30, 42),
    ]
    
    all_passed = True
    
    for n, m in test_pairs:
        phase_n = modular_flow_phase(t, n)
        phase_m = modular_flow_phase(t, m)
        phase_nm = modular_flow_phase(t, n * m)
        
        # Check cocycle property (use symbolic simplification)
        product = sp.simplify(phase_n * phase_m)
        is_cocycle = sp.simplify(product - phase_nm) == 0
        
        if not is_cocycle:
            print(f"❌ FAIL: ({n}*{m})^{{it}} ≠ {n}^{{it}} · {m}^{{it}}")
            print(f"   Left:  {phase_nm}")
            print(f"   Right: {product}")
            all_passed = False
        else:
            print(f"✓ ({n}·{m})^{{it}} = {n}^{{it}} · {m}^{{it}}")
    
    if all_passed:
        print("\n✅ Phase factors form a valid 1-cocycle!\n")
    else:
        print("\n❌ Cocycle property failed!\n")
        return False
    
    return True


def verify_witten_index_structure():
    """
    Demonstrate the Witten index structure.
    
    The Witten index is:
        W = Tr(Γ · e^{-βH}) = Σ_n Γ(n) · n^{-β}
    
    For the Bost-Connes system, this gives:
        W = Σ_n (-1)^{Ω(n)} · n^{-β}
    
    This is related to the Dirichlet series for the Liouville function λ(n) = (-1)^{Ω(n)}.
    """
    print("\n" + "=" * 80)
    print("SYMPY: Witten Index Structure")
    print("=" * 80)
    print("\nComputing partial sums of the Witten index: W(β) = Σ Γ(n) · n^{{-β}}\n")
    
    β = symbols('beta', positive=True, real=True)
    
    # Compute partial sums for N = 10, 20, 50, 100
    limits = [10, 20, 50, 100]
    n = symbols('n')
    
    for N in limits:
        terms = [liouville_grading(k) * k**(-β) for k in range(1, N+1)]
        partial_sum = sum(terms)
        
        print(f"W_{{N={N}}}(β) = {partial_sum}")
        print(f"  Expanded: ", end="")
        expanded_terms = []
        for k in range(1, min(N+1, 11)):
            sign = "+" if liouville_grading(k) > 0 else "-"
            expanded_terms.append(f"{sign} {k}^{{-β}}")
        print(" ".join(expanded_terms[:10]), "..." if N > 10 else "")
        print()
    
    print("Note: The full series converges for Re(β) > 1 and relates to ζ(β) via:")
    print("  Σ λ(n) · n^{{-β}} = ζ(2β) / ζ(β)")
    print("  where λ(n) = (-1)^{Ω(n)} is the Liouville function.\n")


def main():
    """Run all verification tests."""
    print("\n" + "=" * 80)
    print("BOST-CONNES THERMOFIELD DYNAMICS: SYMPY VERIFICATION")
    print("Theorem: Liouville grading Γ commutes with modular flow σ_t")
    print("=" * 80 + "\n")
    
    results = []
    
    # 1. Verify Ω(n) additivity
    results.append(("Ω(n) Additivity", verify_omega_additivity()))
    
    # 2. Verify Γ multiplicativity
    results.append(("Γ Multiplicativity", verify_multiplicativity()))
    
    # 3. Verify phase cocycle
    results.append(("Phase Cocycle", verify_phase_cocycle()))
    
    # 4. Verify commutation on basis
    results.append(("Basis Commutation", verify_commutation_on_basis()))
    
    # 5. Demonstrate Witten index structure
    verify_witten_index_structure()
    
    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    
    all_passed = all(result[1] for result in results)
    
    for name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {name}")
    
    print("\n" + "=" * 80)
    if all_passed:
        print("✅ ALL TESTS PASSED")
        print("\nThe Liouville grading Γ commutes with the modular flow σ_t.")
        print("This confirms the Witten index is invariant under thermal time evolution.")
    else:
        print("❌ SOME TESTS FAILED")
        print("\nReview the failures above.")
    print("=" * 80 + "\n")
    
    return all_passed


if __name__ == "__main__":
    import sys
    success = main()
    sys.exit(0 if success else 1)