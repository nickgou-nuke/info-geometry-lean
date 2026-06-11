import sympy as sp

def verify_biquaternion_isomorphism():
    print("--- Verifying Cl+(3,0; C) -> M_2(C) Isomorphism ---")
    
    i = sp.I
    I = sp.Matrix([[1, 0], [0, 1]])
    
    # User's defined mappings
    K_prime = sp.Matrix([[0, i], [i, 0]])     # phi(e1 e2)
    I_prime = sp.Matrix([[-i, 0], [0, i]])    # phi(e2 e3)
    J_prime = sp.Matrix([[0, -1], [1, 0]])    # phi(e3 e1)
    
    # 1. Check squares
    print("Squares:")
    print("K'^2 =", K_prime**2)
    print("I'^2 =", I_prime**2)
    print("J'^2 =", J_prime**2)
    assert K_prime**2 == -I
    assert I_prime**2 == -I
    assert J_prime**2 == -I
    
    # 2. Check cross products
    # Cl+(3,0) relations:
    # (e1 e2)(e2 e3) = e1 e3 = - e3 e1
    # Thus we expect phi(e1 e2) * phi(e2 e3) = - phi(e3 e1)
    # => K' * I' == -J'
    
    KP_IP = K_prime * I_prime
    expected_neg_JP = -J_prime
    
    print("\nHomomorphism Check 1: phi(e1 e2)*phi(e2 e3) == phi(- e3 e1)")
    print("K' * I' =")
    sp.pprint(KP_IP)
    print("-J' =")
    sp.pprint(expected_neg_JP)
    
    if KP_IP == expected_neg_JP:
        print("PASS")
    else:
        print("FAIL! The user's matrix mapping is NOT a homomorphism.")
        print(f"Error in user exposition: K'*I' is actually {KP_IP}, which is J', not -J' as stated in the text.")

    # 3. Check relation to Pauli matrices
    # sigma_1 = [0, 1; 1, 0]
    # sigma_2 = [0, -i; i, 0]
    # sigma_3 = [1, 0; 0, -1]
    
    sigma_1 = sp.Matrix([[0, 1], [1, 0]])
    sigma_2 = sp.Matrix([[0, -i], [i, 0]])
    sigma_3 = sp.Matrix([[1, 0], [0, -1]])
    
    print("\nPauli Matrix Alignment Check:")
    print("User claims: phi(e1 e2) = i*sigma_3. Actual K' =")
    sp.pprint(K_prime)
    print("i * sigma_3 =")
    sp.pprint(i * sigma_3)
    if K_prime != i * sigma_3:
        print("FAIL: K' is actually i*sigma_1, NOT i*sigma_3.")

if __name__ == "__main__":
    verify_biquaternion_isomorphism()
