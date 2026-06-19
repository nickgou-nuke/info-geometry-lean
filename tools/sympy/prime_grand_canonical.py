import sympy as sp

def analyze_prime_grand_canonical():
    """
    Analyzes the Grand Canonical Ensemble for the prime numbers,
    connecting the partition function to the modular Hamiltonian
    and the Riemann Zeta function.
    """
    # Define symbols
    beta = sp.Symbol('beta', positive=True) # Inverse temperature
    mu = sp.Symbol('mu', real=True)         # Chemical potential
    p = sp.Symbol('p', prime=True)          # Prime number
    
    # Energy of the p-th prime mode is ln(p)
    # The modular Hamiltonian generator
    E_p = sp.ln(p)
    
    # Fugacity z = e^(beta * mu)
    z = sp.exp(beta * mu)
    
    # Single-mode grand canonical partition function (bosonic)
    # Xi_p = sum_{n=0}^infty z^n e^(-beta * n * E_p) = sum_{n=0}^infty (z * p^-beta)^n
    # Xi_p = 1 / (1 - z * p^-beta)
    Xi_p = 1 / (1 - z * p**(-beta))
    
    print("=== Grand Canonical Ensemble of Primes ===")
    print(f"Energy of mode p: E_p = {E_p}")
    print(f"Fugacity: z = {z}")
    print(f"Single mode partition function Xi_p: {Xi_p}")
    
    # Log-partition function for mode p (Grand Potential Omega = - (1/beta) * ln(Xi))
    ln_Xi_p = sp.log(Xi_p)
    print(f"\nLog-partition function for mode p (ln P_p): {sp.simplify(ln_Xi_p)}")
    
    # At chemical potential mu = 0 (z = 1)
    Xi_p_mu0 = Xi_p.subs(mu, 0)
    print(f"\nAt mu = 0 (z = 1), Xi_p: {Xi_p_mu0}")
    
    # The total partition function is the product over all primes
    # Xi = Prod_p Xi_p. This is exactly the Euler product for the Riemann Zeta function when mu = 0!
    # Prod_p 1 / (1 - p^-beta) = zeta(beta)
    print("Total partition function at mu=0 is Prod_p 1/(1 - p^-beta) = zeta(beta)")
    
    # The Modular Hamiltonian K = beta * H
    # The density matrix rho = e^(-K) / Z
    # K is the generator of the modular automorphism group (Tomita-Takesaki)
    print("\n=== Modular Hamiltonian ===")
    print("The modular Hamiltonian K = beta * H, where H|n> = ln(n)|n>")
    print("This generates the time evolution sigma_t(x) = n^(i t) x n^(-i t)")
    
if __name__ == "__main__":
    analyze_prime_grand_canonical()
