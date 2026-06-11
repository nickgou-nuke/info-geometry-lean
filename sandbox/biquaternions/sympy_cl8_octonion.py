import sympy as sp

def generate_octonion_L_matrices():
    """
    Generates the 7 imaginary octonion left-multiplication matrices L_1 ... L_7.
    These are 8x8 real skew-symmetric matrices satisfying L_i L_j + L_j L_i = -2 delta_ij I.
    Basis: 0=1, 1..7 imaginary.
    Fano plane lines: (1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3)
    """
    lines = [
        (1, 2, 4),
        (2, 3, 5),
        (3, 4, 6),
        (4, 5, 7),
        (5, 6, 1),
        (6, 7, 2),
        (7, 1, 3)
    ]
    
    # We build an 8x8x8 multiplication table M[i][j] = k (with sign)
    # where e_i * e_j = sign * e_k
    # 0 is the identity.
    L_matrices = []
    
    for i in range(1, 8):
        # We build an 8x8 matrix for left multiplication by e_i
        mat = sp.zeros(8, 8)
        # e_i * e_0 = e_i
        mat[i, 0] = 1
        # e_i * e_i = -e_0
        mat[0, i] = -1
        
        # Fill in from Fano plane
        for line in lines:
            if i in line:
                idx = line.index(i)
                j = line[(idx + 1) % 3]
                k = line[(idx + 2) % 3]
                # e_i * e_j = e_k
                mat[k, j] = 1
                # e_i * e_k = -e_j
                mat[j, k] = -1
                
        L_matrices.append(mat)
        
    return L_matrices

def verify_cl8():
    print("--- Verifying Cl(0,8; R) ≅ M_16(R) via Octonions ---")
    
    L = generate_octonion_L_matrices()
    
    # Verify L_i are valid Clifford generators for Cl(0,7; R) acting on R^8
    I8 = sp.eye(8)
    cl7_success = True
    for i in range(7):
        for j in range(7):
            anticomm = L[i] * L[j] + L[j] * L[i]
            expected = -2 * I8 if i == j else sp.zeros(8, 8)
            if anticomm != expected:
                cl7_success = False
                print(f"Cl(0,7) relation failed for {i+1}, {j+1}")
                
    if cl7_success:
        print("SUCCESS: 7 imaginary octonions generate Cl(0,7; R) exactly as 8x8 matrices.")
        
    # Build Cl(0,8) using the off-diagonal extension
    print("\nConstructing Cl(0,8; R) 16x16 matrices E_1 ... E_8:")
    E_matrices = []
    
    # E_i = [0, L_i; L_i, 0] for i = 1..7
    for i in range(7):
        E = sp.zeros(16, 16)
        E[0:8, 8:16] = L[i]
        E[8:16, 0:8] = L[i]
        E_matrices.append(E)
        
    # E_8 = [0, I8; -I8, 0]
    E8 = sp.zeros(16, 16)
    E8[0:8, 8:16] = I8
    E8[8:16, 0:8] = -I8
    E_matrices.append(E8)
    
    # Verify Cl(0,8) relations
    I16 = sp.eye(16)
    cl8_success = True
    for i in range(8):
        for j in range(8):
            anticomm = E_matrices[i] * E_matrices[j] + E_matrices[j] * E_matrices[i]
            expected = -2 * I16 if i == j else sp.zeros(16, 16)
            if anticomm != expected:
                cl8_success = False
                print(f"Cl(0,8) relation failed for E_{i+1}, E_{j+1}")
                
    if cl8_success:
        print("SUCCESS: 8 generators E_1 ... E_8 form an exact 16x16 real representation of Cl(0,8; R).")
        print("This explicitly proves Cl(0,8; R) ≅ M_16(R) directly constructed from the Octonion algebra!")
        
if __name__ == "__main__":
    verify_cl8()
