import sympy as sp

def calculate_itakura_saito_primes():
    print("=== SYMPY: ITAKURA-SAITO DIVERGENCE & PRIME LOG-GENERATING POTENTIAL ===")
    
    # Define symbols
    P_n = sp.Symbol('P_n', positive=True) # Prime generating potential (e.g. log zeta)
    Q_n = sp.Symbol('Q_n', positive=True) # Reference potential
    eps = sp.Symbol('epsilon', positive=True) # Regularizer
    
    # 1. Itakura-Saito Divergence
    # D_IS(P || Q) = (P / Q) - log(P / Q) - 1
    # Often used in information geometry for Burg entropy / log-spectra
    D_IS = (P_n / Q_n) - sp.log(P_n / Q_n) - 1
    
    print(f"\n1. Itakura-Saito Divergence D_IS(P_n || Q_n):")
    print(f"   {D_IS}")
    
    # 2. Regularized Partition Function
    # In information geometry, the Bregman generator (Free Energy) is linked to the divergence.
    # Let's define the regularized Free Energy F_eps
    Z_eps = sp.Symbol('Z_eps', positive=True)
    F_eps = -sp.log(Z_eps) - eps * D_IS
    
    print(f"\n2. Regularized Free Energy F_eps = -log(Z_eps) - eps * D_IS:")
    print(f"   {F_eps}")
    
    # 3. Connection to Prime Numbers (Bost-Connes / Zeta)
    # The prime potential is P(s) = sum p^{-s}. Let's assume P_n is the Riemann Zeta partition Z.
    beta = sp.Symbol('beta')
    Z_beta = sp.zeta(beta)
    
    # Substitute P_n -> Z_beta and Q_n -> Z_ref (some reference scale)
    Z_ref = sp.Symbol('Z_ref', positive=True)
    D_IS_zeta = D_IS.subs({P_n: Z_beta, Q_n: Z_ref})
    
    print(f"\n3. Evaluating IS Divergence for Prime Partition Z(beta) = zeta(beta):")
    print(f"   D_IS(Z_beta || Z_ref) = {D_IS_zeta}")
    
    # Calculate gradient of IS Divergence wrt beta (thermodynamic driving force)
    grad_D_IS = sp.diff(D_IS_zeta, beta)
    print(f"\n4. Thermodynamic gradient d/d_beta [D_IS]:")
    print(f"   {grad_D_IS}")
    
    # Evaluating at beta = 2 (the KMS horizon we found earlier)
    # Z(2) = pi^2 / 6
    D_IS_horizon = D_IS_zeta.subs(beta, 2)
    print(f"\n5. Horizon Evaluation (beta = 2):")
    print(f"   D_IS(horizon) = {D_IS_horizon}")
    
if __name__ == "__main__":
    calculate_itakura_saito_primes()
