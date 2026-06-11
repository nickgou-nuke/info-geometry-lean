import sympy as sp

def verify_biquaternion_isomorphism():
    print("--- Fixed Cl+(3,0; C) -> M_2(C) Isomorphism ---")
    
    i = sp.I
    I = sp.Matrix([[1, 0], [0, 1]])
    
    # Correct Pauli Matrices
    sigma_1 = sp.Matrix([[0, 1], [1, 0]])
    sigma_2 = sp.Matrix([[0, -i], [i, 0]])
    sigma_3 = sp.Matrix([[1, 0], [0, -1]])
    
    # Correct mapping
    K_prime = i * sigma_3  # phi(e1 e2)
    I_prime = i * sigma_1  # phi(e2 e3)
    J_prime = i * sigma_2  # phi(e3 e1)
    
    # 1. Check squares
    assert sp.simplify(K_prime**2 + I) == sp.zeros(2, 2)
    assert sp.simplify(I_prime**2 + I) == sp.zeros(2, 2)
    assert sp.simplify(J_prime**2 + I) == sp.zeros(2, 2)
    print("Squares: K'^2 = I'^2 = J'^2 = -I (PASS)")
    
    # 2. Check cross products for homomorphism
    # (e1 e2)(e2 e3) = - e3 e1  => K' * I' == -J'
    assert sp.simplify(K_prime * I_prime - (-J_prime)) == sp.zeros(2, 2)
    # (e2 e3)(e3 e1) = - e1 e2  => I' * J' == -K'
    assert sp.simplify(I_prime * J_prime - (-K_prime)) == sp.zeros(2, 2)
    # (e3 e1)(e1 e2) = - e2 e3  => J' * K' == -I'
    assert sp.simplify(J_prime * K_prime - (-I_prime)) == sp.zeros(2, 2)
    print("Cross Products (Homomorphism): PASS")

    print("\nThe correct representation maps perfectly without sign anomalies.")

if __name__ == "__main__":
    verify_biquaternion_isomorphism()
