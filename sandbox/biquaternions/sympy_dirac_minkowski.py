import sympy as sp

def verify_dirac_algebra():
    print("--- SymPy Verification of Dirac Gamma Matrices (Cl(1,3; C)) ---")
    
    i = sp.I
    
    # Define the 4x4 Gamma matrices (Dirac representation)
    g0 = sp.Matrix([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, -1, 0],
        [0, 0, 0, -1]
    ])
    
    g1 = sp.Matrix([
        [0, 0, 0, 1],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [-1, 0, 0, 0]
    ])
    
    g2 = sp.Matrix([
        [0, 0, 0, -i],
        [0, 0, i, 0],
        [0, i, 0, 0],
        [-i, 0, 0, 0]
    ])
    
    g3 = sp.Matrix([
        [0, 0, 1, 0],
        [0, 0, 0, -1],
        [-1, 0, 0, 0],
        [0, 1, 0, 0]
    ])
    
    gammas = [g0, g1, g2, g3]
    
    # Minkowski metric eta (diag(1, -1, -1, -1))
    eta = sp.diag(1, -1, -1, -1)
    
    I4 = sp.eye(4)
    
    success = True
    print("\nVerifying Jordan product (anticommutator) {g^u, g^v} = 2 * eta^uv * I")
    for mu in range(4):
        for nu in range(4):
            # Compute anticommutator
            anticomm = gammas[mu] * gammas[nu] + gammas[nu] * gammas[mu]
            
            # Expected result
            expected = 2 * eta[mu, nu] * I4
            
            if anticomm != expected:
                print(f"FAILED for mu={mu}, nu={nu}")
                success = False
                
    if success:
        print("SUCCESS: All 16 anticommutation relations hold exactly.")
        print("The Jordan product perfectly recovers the Minkowski metric g_ij = (1/2){e_i, e_j}.")
    
    print("\nVerifying Complexified Clifford Algebra Isomorphism Cl(1,3; C) ≅ M4(C)")
    print("The 16 basis elements (1, g^u, g^u g^v, g^u g^v g^l, g^0 g^1 g^2 g^3) are linearly independent.")
    
    # Let's verify linear independence of the 16 matrices
    basis_matrices = [I4]
    
    # 1-vectors
    for mu in range(4):
        basis_matrices.append(gammas[mu])
        
    # 2-vectors
    for mu in range(4):
        for nu in range(mu+1, 4):
            basis_matrices.append(gammas[mu] * gammas[nu])
            
    # 3-vectors
    for mu in range(4):
        for nu in range(mu+1, 4):
            for rho in range(nu+1, 4):
                basis_matrices.append(gammas[mu] * gammas[nu] * gammas[rho])
                
    # 4-vector (pseudoscalar)
    basis_matrices.append(gammas[0] * gammas[1] * gammas[2] * gammas[3])
    
    # Convert each 4x4 matrix into a 16-dimensional vector to check linear independence
    # We construct a 16x16 matrix where each row is one of our basis matrices flattened
    vecs = [m.reshape(1, 16) for m in basis_matrices]
    M = sp.Matrix.vstack(*vecs)
    
    det_M = M.det()
    print(f"Determinant of the 16x16 basis transformation matrix: {det_M}")
    if det_M != 0:
        print("SUCCESS: The 16 Clifford basis matrices span the entire M4(C) space, confirming Cl(1,3; C) ≅ M4(C).")
    else:
        print("FAILED: The basis matrices are not linearly independent.")

if __name__ == "__main__":
    verify_dirac_algebra()
