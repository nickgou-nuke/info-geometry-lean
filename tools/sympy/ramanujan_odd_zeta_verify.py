import sympy as sp
import math

def verify_ramanujan_odd_zeta():
    print("RAMANUJAN'S ODD ZETA FORMULA — SymPy VERIFICATION\n")
    
    # We verify the formula numerically for n = 1 (zeta(3))
    # Formula: alpha^(-n) * (1/2 * zeta(2n+1) + sum_k k^(-(2n+1))/(exp(2*alpha*k)-1)) =
    #          (-beta)^(-n) * (1/2 * zeta(2n+1) + sum_k k^(-(2n+1))/(exp(2*beta*k)-1)) -
    #          2^(2n) * sum_{k=0}^{n+1} (-1)^k B_{2k}/(2k)! B_{2n+2-2k}/(2n+2-2k)! alpha^(n+1-k) beta^k
    
    n = 1
    # Choose alpha and beta such that alpha * beta = pi^2
    # Let's pick alpha = pi, beta = pi
    alpha = math.pi
    beta = math.pi
    
    # Calculate zeta(3)
    zeta3 = float(sp.zeta(3).evalf())
    
    # Calculate LHS infinite sum (approximate to 100 terms for high precision)
    sum_lhs = 0.0
    for k in range(1, 101):
        term = (k**(-3)) / (math.exp(2 * alpha * k) - 1)
        sum_lhs += term
        
    lhs = (alpha**(-n)) * (0.5 * zeta3 + sum_lhs)
    
    # Calculate RHS infinite sum (same as LHS since alpha=beta)
    sum_rhs = 0.0
    for k in range(1, 101):
        term = (k**(-3)) / (math.exp(2 * beta * k) - 1)
        sum_rhs += term
        
    term1_rhs = ((-beta)**(-n)) * (0.5 * zeta3 + sum_rhs)
    
    # Calculate RHS finite sum
    sum_bernoulli = 0.0
    for k in range(n + 2):
        b_2k = float(sp.bernoulli(2 * k))
        fact_2k = math.factorial(2 * k)
        
        idx2 = 2 * n + 2 - 2 * k
        b_2n2k = float(sp.bernoulli(idx2))
        fact_2n2k = math.factorial(idx2)
        
        term = ((-1)**k) * (b_2k / fact_2k) * (b_2n2k / fact_2n2k) * (alpha**(n + 1 - k)) * (beta**k)
        sum_bernoulli += term
        
    term2_rhs = (2**(2 * n)) * sum_bernoulli
    
    rhs = term1_rhs - term2_rhs
    
    print(f"Testing for n = {n}, alpha = pi, beta = pi")
    print(f"LHS = {lhs}")
    print(f"RHS = {rhs}")
    
    if abs(lhs - rhs) < 1e-10:
        print("\nSUCCESS: Ramanujan's odd zeta formula is VERIFIED numerically.")
    else:
        print("\nFAILURE: Mismatch found.")

if __name__ == "__main__":
    verify_ramanujan_odd_zeta()
