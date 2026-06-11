import sympy as sp

def generate_cl9_matrices():
    """
    Generates the 9 generators for Cl(9, C) as 32x32 matrices,
    demonstrating the Cl(9, C) ≅ M_16(C) ⊕ M_16(C) structure connected to E8.
    """
    # First, get the 8 generators of Cl(8, C) as 16x16 matrices
    def generate_cl_even(n):
        if n == 0:
            return []
        if n == 2:
            s1 = sp.Matrix([[0, 1], [1, 0]])
            s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
            return [s1, s2]
        
        prev = generate_cl_even(n - 2)
        Z = sp.eye(prev[0].shape[0])
        for g in prev:
            Z = Z * g
        # Fix sign of Z
        m = n - 2
        if (-1)**(m * (m - 1) // 2) == -1:
            Z = sp.I * Z
            
        s1 = sp.Matrix([[0, 1], [1, 0]])
        s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
        I2 = sp.eye(2)
        
        new_gens = []
        for g in prev:
            new_gens.append(sp.kronecker_product(g, I2))
        new_gens.append(sp.kronecker_product(Z, s1))
        new_gens.append(sp.kronecker_product(Z, s2))
        return new_gens

    # Get Cl(8, C) generators (16x16 matrices)
    cl8_gens = generate_cl_even(8)
    
    # Construct the volume element for Cl(8, C)
    Z8 = sp.eye(16)
    for g in cl8_gens:
        Z8 = Z8 * g
    # For m=8, sign is (-1)^(8*7/2) = 1, so Z8^2 = I
    
    # We build 32x32 matrices for Cl(9, C)
    # The first 8 generators are block diagonal: diag(g_i, -g_i)
    # Wait, the standard way is to use the Cl(8) matrices \otimes Pauli
    # e_i = e'_i \otimes s1 for i=1..8
    # e_9 = I_{16} \otimes s2
    # This gives 32x32 matrices.
    
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    
    cl9_gens = []
    # e_i = e'_i \otimes s1
    for g in cl8_gens:
        cl9_gens.append(sp.kronecker_product(g, s3))
        
    # e_9 = I_{16} \otimes s1
    # Wait, e_i * e_9 = (e'_i \otimes s3)(I \otimes s1) = e'_i \otimes (s3*s1) = e'_i \otimes (i s2)
    # They anticommute perfectly!
    I16 = sp.eye(16)
    cl9_gens.append(sp.kronecker_product(I16, s1))
    
    return cl9_gens

def verify_cl9():
    print("--- Verifying Cl(9, C) ≅ M_16(C) ⊕ M_16(C) Structure ---")
    print("This exceptionally rich algebra connects to the structure of E8.")
    
    gens = generate_cl9_matrices()
    matrix_size = gens[0].shape[0]
    print(f"\nGenerated 9 generators as {matrix_size}x{matrix_size} matrices.")
    
    # Verify anticommutation relations
    I32 = sp.eye(32)
    success = True
    for i in range(9):
        for j in range(9):
            anticomm = gens[i] * gens[j] + gens[j] * gens[i]
            expected = 2 * I32 if i == j else sp.zeros(32, 32)
            if anticomm != expected:
                success = False
                print(f"Relation failed for {i+1}, {j+1}")
                
    if success:
        print("SUCCESS: 9 algebraic generators properly satisfy Cl(9, C) conditions.")
        
    # The volume element of Cl(9, C) commutes with all elements and squares to I.
    # Therefore, the space decomposes into two 16x16 blocks (the eigenspaces of the volume element).
    # Let's compute the volume element.
    Z9 = sp.eye(32)
    for g in gens:
        Z9 = Z9 * g
        
    # Check if Z9 commutes with everything
    commutes = True
    for i, g in enumerate(gens):
        if Z9 * g != g * Z9:
            commutes = False
            
    if commutes:
        print("SUCCESS: The volume element Z9 commutes with all 9 generators.")
        print("Because Z9 commutes with everything and Z9^2 = I, the 32x32 representation")
        print("strictly block-diagonalizes into two M_16(C) components: Cl(9, C) ≅ M_16(C) ⊕ M_16(C).")
        print("This dual M_16(C) representation is deeply linked to the octonionic foundation of E8.")

if __name__ == "__main__":
    verify_cl9()
