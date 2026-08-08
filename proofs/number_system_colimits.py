import sympy as sp

def define_colimits():
    # 1. Primes
    primes = sp.S.Primes
    print(f"Base limit (Primes): {primes}")
    
    # 2. N (Naturals)
    N = sp.S.Naturals
    print(f"Free commutative monoid (Naturals): {N}")
    
    # 3. Q (Rationals)
    Q = sp.S.Rationals
    print(f"Localization (Rationals): {Q}")
    
    # 4. R (Reals)
    R = sp.S.Reals
    print(f"Completion (Reals): {R}")
    
    # 5. C (Complexes)
    C = sp.S.Complexes
    print(f"Pushout (Complexes): {C}")
    
    # Riemann Zeta Zeroes
    s = sp.Symbol('s')
    zeta = sp.zeta(s)
    print(f"Zeta function: {zeta}")
    print("Zeta zeroes natively reside in the C pushout space constrained by the prime coproduct.")

if __name__ == "__main__":
    define_colimits()
