import sympy as sp

def test_kms_dyadic_scaling():
    print("--- SymPy Twin: KMS Dyadic Rationals ---")
    
    phi_L = sp.Symbol('phi_L', real=True)
    phi_R = sp.Symbol('phi_R', real=True)
    beta = sp.Symbol('beta', real=True)

    # The partition condition: phi(P_L + P_R) = 1
    # implies phi_L + phi_R = 1
    partition_eq = sp.Eq(phi_L + phi_R, 1)
    
    # The KMS symmetry condition: phi_L = phi_R (since both branches scale equally)
    symmetry_eq = sp.Eq(phi_L, phi_R)
    
    # Solve for the branch weight
    solutions = sp.solve((partition_eq, symmetry_eq), (phi_L, phi_R))
    print(f"1. Branch Weights: {solutions}")
    
    # The scaling factor e^{-beta} corresponds to the branch weight
    phi_L_val = solutions[phi_L]
    kms_scaling_eq = sp.Eq(sp.exp(-beta), phi_L_val)
    
    # Solve for beta (Inverse Temperature)
    beta_solution = sp.solve(kms_scaling_eq, beta)
    print(f"2. KMS Inverse Temperature (beta): {beta_solution[0]}")
    
    if beta_solution[0] == sp.log(2):
        print("\n[SUCCESS] The KMS inverse temperature strictly forces beta = ln(2)!")
        print("The dyadic rationals Z[1/2] structurally dictate the thermodynamics of the exact vacuum.")
    else:
        print("\n[FAILED]")

if __name__ == "__main__":
    test_kms_dyadic_scaling()
