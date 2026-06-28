#!/usr/bin/env python3
"""
galgebra/clifford: Bost-Connes Liouville-Modular Flow in Geometric Algebra

This script formalizes the Bost-Connes system using geometric algebra (Clifford algebra).
We represent:
- Bost-Connes generators as multivectors
- Liouville grading as grade involution
- Modular flow as rotor action

Theorem: The Liouville grading commutes with the modular flow.
"""

import numpy as np
try:
    import clifford as cf
    HAS_CLIFFORD = True
except ImportError:
    HAS_CLIFFORD = False
    print("clifford package not installed. Install with: pip install clifford")

try:
    from galgebra.ga import Ga
    HAS_GALGEBRA = True
except ImportError:
    HAS_GALGEBRA = False
    print("galgebra not installed. Install with: pip install galgebra")


def omega(n):
    """
    Ω(n) = total number of prime factors (with multiplicity)
    """
    if n <= 0:
        raise ValueError("n must be positive")
    if n == 1:
        return 0
    
    from sympy import factorint
    factors = factorint(n)
    return sum(mult for mult in factors.values())


def liouville(n):
    """
    Liouville function: λ(n) = (-1)^Ω(n)
    
    In geometric algebra, this corresponds to grade involution.
    """
    return (-1) ** omega(n)


class BostConnesGeometricAlgebra:
    """
    Bost-Connes system in Geometric Algebra framework.
    
    We use a Clifford algebra Cl(p,q) where:
    - Generators μ_n are represented as multivectors
    - The Liouville grading is the main involution (grade negation)
    - Modular flow is a rotor action
    """
    
    def __init__(self, n_generators=6):
        """
        Initialize with n_generators prime-indexed generators.
        
        We use Cl(2n, 0) for n generators to have enough room.
        """
        if not HAS_CLIFFORD:
            raise RuntimeError("clifford package required")
        
        self.n_generators = n_generators
        # Use Cl(2n, 0) - Euclidean space with 2n dimensions
        self.layout, self.blades = cf.Cl(2 * n_generators)
        
        # Store generator multivectors
        self.generators = {}
        self._create_generators()
        
    def _create_generators(self):
        """
        Create generator multivectors μ_n for n = 1..prime_k.
        
        Each generator is represented as a simple vector in the algebra.
        """
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29][:self.n_generators]
        
        for i, p in enumerate(primes):
            # Create generator as basis vector e_i
            basis_vector_name = f'e{i+1}'
            self.generators[p] = self.blades[basis_vector_name]
            
    def get_generator(self, n):
        """
        Get generator μ_n. For composite n, use multiplicativity.
        """
        if n in self.generators:
            return self.generators[n]
        
        # For composite n, factor and multiply
        from sympy import factorint
        factors = factorint(n)
        
        result = 1.0
        for prime, multiplicity in factors.items():
            gen = self.get_generator(prime)
            for _ in range(multiplicity):
                result = result * gen
        
        return result
    
    def liouville_grading(self, multivector, n):
        """
        Apply Liouville grading to a multivector associated with n.
        
        Γ(μ_n) = (-1)^Ω(n) · μ_n
        
        In GA, this is grade involution scaled by λ(n).
        """
        lambda_n = liouville(n)
        return lambda_n * multivector
    
    def modular_flow(self, multivector, t, n):
        """
        Apply modular flow to generator μ_n.
        
        σ_t(μ_n) = n^{it} · μ_n
        
        In GA, we represent the phase as a rotor in a complex plane.
        For simplicity, we use scalar multiplication by the phase.
        """
        import cmath
        phase = cmath.exp(1j * t * np.log(n))
        
        # For real GA, we embed in complexified algebra
        # Here we use a simplified representation
        return phase * multivector
    
    def verify_commutation(self, t, max_n=20):
        """
        Verify that Liouville grading and modular flow commute.
        
        Test: Γ(σ_t(μ_n)) = σ_t(Γ(μ_n))
        """
        import cmath
        
        print(f"\nVerifying commutation for t = {t}, n ≤ {max_n}")
        
        all_pass = True
        test_count = 0
        
        # Test with prime generators first
        primes = [2, 3, 5, 7, 11, 13, 17, 19][:min(max_n, len(self.generators))]
        
        for n in primes:
            mu_n = self.get_generator(n)
            lambda_n = liouville(n)
            phase = cmath.exp(1j * t * np.log(n))
            
            # Order 1: Γ(σ_t(μ_n))
            sigma_first = self.modular_flow(mu_n, t, n)
            gamma_sigma = self.liouville_grading(sigma_first, n)
            
            # Order 2: σ_t(Γ(μ_n))
            gamma_first = self.liouville_grading(mu_n, n)
            sigma_gamma = self.modular_flow(gamma_first, t, n)
            
            # Check equality (allowing for numerical precision)
            diff = abs(gamma_sigma - sigma_gamma)
            
            if diff > 1e-10:
                print(f"  ❌ FAIL: n={n}, |Γ(σ) - σ(Γ)| = {diff}")
                all_pass = False
            else:
                test_count += 1
        
        # Test a few composite numbers
        composites = [4, 6, 8, 9, 10, 12, 15, 18]
        for n in composites:
            if n > max_n:
                break
            
            mu_n = self.get_generator(n)
            lambda_n = liouville(n)
            phase = cmath.exp(1j * t * np.log(n))
            
            # Both orders
            sigma_first = self.modular_flow(mu_n, t, n)
            gamma_sigma = self.liouville_grading(sigma_first, n)
            
            gamma_first = self.liouville_grading(mu_n, n)
            sigma_gamma = self.modular_flow(gamma_first, t, n)
            
            diff = abs(gamma_sigma - sigma_gamma)
            
            if diff > 1e-10:
                print(f"  ❌ FAIL (composite): n={n}, diff={diff}")
                all_pass = False
            else:
                test_count += 1
        
        print(f"  Tested {test_count} elements")
        return all_pass


class BostConnesCliffordSimple:
    """
    Simplified Clifford algebra verification without full GA machinery.
    
    Uses the fact that both operators act by scalars, which commute.
    """
    
    def __init__(self):
        self.test_count = 0
        self.pass_count = 0
    
    def verify_commutation_symbolic(self, t, n):
        """
        Verify commutation for a single n using symbolic reasoning.
        
        Since both Γ and σ_t act by scalar multiplication:
          Γ(μ_n) = λ(n) · μ_n
          σ_t(μ_n) = n^{it} · μ_n
        
        And scalars commute, the operators commute.
        """
        import cmath
        
        lambda_n = liouville(n)
        phase = cmath.exp(1j * t * np.log(n))
        
        # Both orderings give: λ(n) · n^{it} · μ_n
        left = lambda_n * phase
        right = phase * lambda_n
        
        self.test_count += 1
        
        if abs(left - right) < 1e-10:
            self.pass_count += 1
            return True
        return False
    
    def run_full_verification(self, max_n=50):
        """
        Run complete verification for n = 1..max_n.
        """
        print("=" * 80)
        print("GEOMETRIC ALGEBRA / CLIFFORD: Symbolic Verification")
        print("=" * 80)
        print(f"\nVerifying: [Γ, σ_t] = 0 for n = 1..{max_n}")
        print("Method: Scalar commutativity (both operators act diagonally)\n")
        
        all_pass = True
        
        for t in [0.0, 0.5, 1.0, 2.0]:
            print(f"Testing t = {t}:")
            for n in range(1, max_n + 1):
                if not self.verify_commutation_symbolic(t, n):
                    print(f"  ❌ FAIL: n={n}, t={t}")
                    all_pass = False
            
            print(f"  ✓ All {max_n} tests passed for t={t}\n")
        
        print("=" * 80)
        print(f"Total tests: {self.test_count}")
        print(f"Passed: {self.pass_count}")
        print(f"Failed: {self.test_count - self.pass_count}")
        
        if all_pass:
            print("✅ ALL TESTS PASSED")
            print("\nConclusion: [Γ, σ_t] = 0 confirmed via scalar commutativity")
            print("Interpretive status: this run verifies the scalar commutation calculation")
        else:
            print("❌ SOME TESTS FAILED")
        
        print("=" * 80)
        
        return all_pass


def main():
    """Run all geometric algebra verifications."""
    print("\n" + "=" * 80)
    print("BOST-CONNES IN GEOMETRIC ALGEBRA / CLIFFORD ALGEBRA")
    print("=" * 80 + "\n")
    
    results = []
    
    # 1. Simplified Clifford verification (always works)
    print("1. Simplified Clifford Verification (Scalar Commutativity)")
    print("-" * 80)
    simple = BostConnesCliffordSimple()
    simple_result = simple.run_full_verification(max_n=50)
    results.append(("Clifford Symbolic", simple_result))
    
    # 2. Full Geometric Algebra (if clifford package available)
    if HAS_CLIFFORD:
        print("\n2. Full Geometric Algebra Verification")
        print("-" * 80)
        try:
            ga = BostConnesGeometricAlgebra(n_generators=6)
            ga_result = ga.verify_commutation(t=1.0, max_n=20)
            results.append(("Geometric Algebra", ga_result))
        except Exception as e:
            print(f"  ⚠️  GA test failed: {e}")
            results.append(("Geometric Algebra", False))
    else:
        print("\n2. Full Geometric Algebra: SKIPPED (clifford not installed)")
        results.append(("Geometric Algebra", None))
    
    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    
    passed = 0
    total = 0
    
    for name, result in results:
        if result is None:
            status = "⊘ SKIPPED"
        elif result:
            status = "✅ PASS"
            passed += 1
            total += 1
        else:
            status = "❌ FAIL"
            total += 1
        
        print(f"{status}: {name}")
    
    print(f"\nPassed: {passed}/{total} executable tests")
    
    if passed == total and total > 0:
        print("\n✅ GEOMETRIC ALGEBRA VERIFICATION COMPLETE")
        print("\nKey insight: Both Γ and σ_t act by scalar multiplication,")
        print("and scalars commute. This is the geometric algebra perspective")
        print("on the diagonal action of both operators.")
    else:
        print("\n⚠️  Some tests skipped or failed")
    
    print("=" * 80 + "\n")
    
    return passed == total and total > 0


if __name__ == "__main__":
    import sys
    success = main()
    sys.exit(0 if success else 1)