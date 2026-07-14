# bost_connes_gns.sage
# Programmatic evaluation of the GNS Hilbert Space representations 
# computationally modeling the phase transitions in the Bost-Connes system.

import math

def riemann_zeta_eval(beta, terms=1000):
    """
    Evaluate the Riemann Zeta function numerically for the partition function.
    Valid for beta > 1.
    """
    if beta <= 1:
        return float('inf')
    # Using Sage's native zeta function
    return zeta(beta).n()

def kms_state_low_temp(beta, n, gamma):
    r"""
    Evaluates the KMS state on the generator \mu_n * e(gamma) for beta > 1.
    For beta > 1, the KMS states are parameterized by embeddings of Q(mu_infty) into C.
    The partition function is zeta(beta).
    """
    if beta <= 1:
        raise ValueError("Beta must be > 1 for the low temperature phase.")
    
    # Trace over the GNS Hilbert space gives non-zero only for n=1
    if n != 1:
        return 0
    
    # For n=1, state(e(gamma)) = sum_{k=1}^infty k^{-beta} * (1 if k*gamma in Z else 0) / zeta(beta)
    # We truncate the infinite sum to `terms` for computational modeling.
    terms = 1000
    z = riemann_zeta_eval(beta)
    
    # We represent gamma as a rational a/b
    # k * (a/b) in Z <=> b divides k
    b = gamma.denominator()
    
    # Sum over multiples of b
    val = sum([ (m*b)^(-beta) for m in range(1, (terms // b) + 2) ])
    
    return float(val / z)

def kms_state_high_temp(beta, n, gamma):
    """
    Evaluates the unique KMS state for beta <= 1.
    The state vanishes on e(gamma) unless gamma in Z.
    """
    if n != 1:
        return 0
    if gamma not in ZZ:
        return 0
    return 1.0

def evaluate_bost_connes_model():
    print("Evaluating Bost-Connes Phase Transitions...")
    gammas = [QQ(1/2), QQ(1/3), QQ(1/4)]
    
    print("\n--- High Temperature Phase (beta <= 1) ---")
    beta_high = 0.5
    print(f"Beta = {beta_high}")
    for gamma in gammas:
        val = kms_state_high_temp(beta_high, 1, gamma)
        print(f"KMS(e({gamma})) = {val}")
        
    print("\n--- Low Temperature Phase (beta > 1) ---")
    beta_low = 2.0
    print(f"Beta = {beta_low}")
    print(f"Partition Function Z({beta_low}) = {riemann_zeta_eval(beta_low):.4f}")
    for gamma in gammas:
        val = kms_state_low_temp(beta_low, 1, gamma)
        print(f"KMS(e({gamma})) = {val:.4f}")

evaluate_bost_connes_model()
