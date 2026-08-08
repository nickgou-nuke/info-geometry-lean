import sympy as sp
from sympy.ntheory import mobius, divisors

def dirichlet_convolution(f, g, n):
    """
    Computes the Dirichlet convolution of two arithmetic functions f and g evaluated at n.
    (f * g)(n) = sum_{d|n} f(d) * g(n/d)
    """
    return sum(f(d) * g(n // d) for d in divisors(n))

def constant_one(n):
    """
    The constant function 1. Represents the macroscopic Bosonic sum.
    """
    return 1

def epsilon(n):
    """
    The identity function for Dirichlet convolution.
    Represents the supersymmetric vacuum state |1>.
    ε(1) = 1, ε(n) = 0 for n > 1.
    """
    return 1 if n == 1 else 0

def test_susy_annihilation():
    print("--- Supersymmetric Vacuum Annihilation Witness (SymPy) ---")
    print("Verifying that Bosonic Trace (1) * Fermionic Parity (μ) = Vacuum (ε)\n")
    
    # Test up to n=20 to prove it computationally
    success = True
    for n in range(1, 21):
        # Convolve Möbius (Fermions) with Constant 1 (Bosons)
        annihilation_result = int(dirichlet_convolution(mobius, constant_one, n))
        vacuum_expected = epsilon(n)
        
        print(f"State |{n:2}>: μ * 1 = {annihilation_result:2} | Expected Vacuum = {vacuum_expected}")
        if annihilation_result != vacuum_expected:
            success = False

    print("\n[RESULT]:", "VERIFIED! All macroscopic states perfectly annihilated into the vacuum." if success else "FAILED")

def test_mobius_inversion():
    print("\n--- Möbius Inversion Transform Witness (SymPy) ---")
    
    # Define an arbitrary irreducible Fermionic generator function f(n)
    # E.g., f(n) = n
    def f(n):
        return n
    
    # Apply the 'Bosonic' macroscopic sum over divisors to create g(n)
    def g(n):
        return int(dirichlet_convolution(f, constant_one, n))
        
    print("Let irreducible Fermionic generator f(n) = n")
    print("Let macroscopic Bosonic observable g(n) = sum_{d|n} f(d)")
    print("Applying Möbius Inversion to recover f(n) from g(n)...\n")
    
    success = True
    for n in range(1, 21):
        # We only know g(n). We apply the Möbius inversion transform to recover f.
        recovered_f = int(dirichlet_convolution(g, mobius, n))
        actual_f = f(n)
        
        print(f"State |{n:2}>: g(n) = {g(n):3}  =>  Recovered f(n) = {recovered_f:2}  | Actual = {actual_f}")
        if recovered_f != actual_f:
            success = False

    print("\n[RESULT]:", "VERIFIED! The Möbius discrete integral transform perfectly recovered the irreducible generators." if success else "FAILED")

if __name__ == "__main__":
    test_susy_annihilation()
    test_mobius_inversion()
