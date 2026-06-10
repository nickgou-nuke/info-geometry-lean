import sympy as sp
import math

def verify_equivalences():
    print("RIEMANN ZETA EQUIVALENT REPRESENTATIONS — SymPy VERIFICATION\n")
    
    s = sp.Symbol('s')
    
    # SymPy's builtin Riemann Zeta
    zeta_s = sp.zeta(s)
    
    # 1. Dirichlet Eta Quotient
    eta_s = sp.dirichlet_eta(s)
    zeta_from_eta = eta_s / (1 - 2**(1-s))
    
    # We evaluate numerically at a test point in the region Re(s) > 0, e.g. s = 3.5
    test_val = 3.5
    zeta_num = zeta_s.subs(s, test_val).evalf()
    zeta_eta_num = zeta_from_eta.subs(s, test_val).evalf()
    
    print(f"1. Eta Quotient Definition: zeta(s) = eta(s) / (1 - 2^(1-s))")
    print(f"   At s = {test_val}:")
    print(f"   zeta(s)       = {zeta_num}")
    print(f"   From eta(s)   = {zeta_eta_num}")
    if abs(zeta_num - zeta_eta_num) < 1e-10:
        print("   SUCCESS: Eta Quotient definition matches Riemann Zeta.\n")
    else:
        print("   FAILURE.\n")
        
    # 2. Dirichlet Series (Finite sum approximation for convergence check)
    # zeta(s) = sum_{n=1}^infty n^(-s)
    N_approx = 10000
    dirichlet_approx = sum([n**(-test_val) for n in range(1, N_approx+1)])
    print(f"2. Dirichlet Series Definition: zeta(s) = sum n^(-s)")
    print(f"   Approximated with {N_approx} terms at s = {test_val}:")
    print(f"   zeta(s)            = {zeta_num}")
    print(f"   Dirichlet Series   = {dirichlet_approx}")
    if abs(zeta_num - dirichlet_approx) < 1e-4:
        print("   SUCCESS: Dirichlet series converges to Riemann Zeta.\n")
    else:
        print("   FAILURE.\n")
        
    # 3. Euler Product (Finite product approximation)
    # zeta(s) = prod_{p} (1 - p^(-s))^-1
    primes = list(sp.primerange(2, N_approx))
    euler_approx = 1.0
    for p in primes:
        euler_approx *= 1 / (1 - p**(-test_val))
    print(f"3. Euler Product Definition: zeta(s) = prod (1 - p^(-s))^-1")
    print(f"   Approximated with primes < {N_approx} at s = {test_val}:")
    print(f"   zeta(s)            = {zeta_num}")
    print(f"   Euler Product      = {euler_approx}")
    if abs(zeta_num - euler_approx) < 1e-4:
        print("   SUCCESS: Euler product converges to Riemann Zeta.\n")
    else:
        print("   FAILURE.\n")

if __name__ == "__main__":
    verify_equivalences()
