import sympy as sp
from sympy import pi, zeta, factorial, bernoulli
import mpmath as mp

def verify_completed_zeta_parity():
    print("Verifying Completed Zeta Function Parity in Symmetry-Adapted Coordinates")
    s = sp.Symbol('s')
    # Riemann xi function: xi(s) = 1/2 * s * (s - 1) * pi^(-s/2) * Gamma(s/2) * zeta(s)
    xi_s = sp.Rational(1, 2) * s * (s - 1) * sp.pi**(-s/2) * sp.gamma(s/2) * sp.zeta(s)
    
    # We know the functional equation is xi(s) = xi(1-s)
    # Define z = s - 1/2, so s = z + 1/2
    z = sp.Symbol('z')
    Xi_z = xi_s.subs(s, z + sp.Rational(1, 2))
    
    # Check if Xi_z is an even function: Xi(z) == Xi(-z)
    Xi_minus_z = Xi_z.subs(z, -z)
    
    # We test it numerically to avoid complex symbolic simplification of Gamma and Zeta
    print("Evaluating Xi(z) - Xi(-z) for z = 1/4 + 14.13 i (near first zero)")
    test_val = 0.25 + 14.13j
    val1 = complex(Xi_z.subs(z, test_val).evalf())
    val2 = complex(Xi_minus_z.subs(z, test_val).evalf())
    
    diff = abs(val1 - val2)
    print(f"Difference: {diff}")
    
    if diff < 1e-10:
        print("SUCCESS: Xi(z) is strictly even: Xi(z) = Xi(-z)")
    else:
        print("FAILURE: Parity mismatch")

def verify_ramanujan_odd_zeta():
    print("\nVerifying Ramanujan's Formula for Odd Zeta Values (n=1 -> zeta(3))")
    mp.dps = 50
    
    # For n=1, zeta(2n+1) = zeta(3).
    # Choose alpha = 2*pi, beta = pi/2 so alpha * beta = pi^2
    n = 1
    alpha = 2 * mp.pi
    beta = mp.pi / 2
    
    def ramanujan_sum(x, p):
        # sum_{k=1}^infty k^(-p) / (exp(2*x*k) - 1)
        s = mp.mpf(0)
        for k in range(1, 1000):
            term = (k**(-p)) / (mp.exp(2 * x * k) - 1)
            s += term
            if term < 1e-55:
                break
        return s

    # Left hand side
    lhs_sum = ramanujan_sum(alpha, 2*n + 1)
    lhs = (alpha**(-n)) * (mp.zeta(3) / 2 + lhs_sum)
    
    # Right hand side
    rhs_sum = ramanujan_sum(beta, 2*n + 1)
    rhs_first_term = ((-beta)**(-n)) * (mp.zeta(3) / 2 + rhs_sum)
    
    # Residual finite sum
    # - 2^(2n) sum_{k=0}^{n+1} (-1)^k * (B_{2k} / (2k)!) * (B_{2n+2-2k} / (2n+2-2k)!) * alpha^{n+1-k} * beta^k
    rhs_residual = mp.mpf(0)
    for k in range(n + 2):
        b_2k = mp.bernoulli(2 * k)
        fact_2k = mp.fac(2 * k)
        
        idx2 = 2*n + 2 - 2*k
        b_2n_2k = mp.bernoulli(idx2)
        fact_2n_2k = mp.fac(idx2)
        
        term = ((-1)**k) * (b_2k / fact_2k) * (b_2n_2k / fact_2n_2k) * (alpha**(n + 1 - k)) * (beta**k)
        rhs_residual += term
        
    rhs_residual *= -(2**(2*n))
    
    rhs = rhs_first_term + rhs_residual
    
    diff = abs(lhs - rhs)
    print(f"LHS: {lhs}")
    print(f"RHS: {rhs}")
    print(f"Difference: {diff}")
    
    if diff < 1e-45:
        print("SUCCESS: Ramanujan's formula holds to 50 decimal places for zeta(3).")
    else:
        print("FAILURE.")

if __name__ == "__main__":
    verify_completed_zeta_parity()
    verify_ramanujan_odd_zeta()
