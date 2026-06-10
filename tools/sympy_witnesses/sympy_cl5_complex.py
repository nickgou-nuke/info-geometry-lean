import sympy as sp
from sympy.physics.quantum import TensorProduct

def verify_cl5_complex():
    print("--- Verifying Cl(5,0; C) -> M_4(C) x M_4(C) Isomorphism ---")
    
    # Pauli matrices
    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    
    # 4x4 Generators for Cl4
    g1 = TensorProduct(s1, I2)
    g2 = TensorProduct(s2, I2)
    g3 = TensorProduct(s3, s1)
    g4 = TensorProduct(s3, s2)
    
    # Volume element of Cl4
    g5 = g1 * g2 * g3 * g4
    
    # Check that g5 anticommutes with g1..g4 and g5^2 = I
    print("\nChecking auxiliary g5 properties:")
    print("g5^2 == I:", sp.simplify(g5*g5) == sp.eye(4))
    for i, g in enumerate([g1, g2, g3, g4]):
        print(f"g5*g_{i+1} + g_{i+1}*g5 == 0:", sp.simplify(g5*g + g*g5) == sp.zeros(4))
    
    # Now construct Cl5 generators in M_4(C) x M_4(C)
    # We represent pairs (A, B) as block diagonal 8x8 matrices to easily calculate ranks
    def block_diag(A, B):
        return sp.Matrix(sp.BlockDiagMatrix(A, B))
        
    e1 = block_diag(g1, g1)
    e2 = block_diag(g2, g2)
    e3 = block_diag(g3, g3)
    e4 = block_diag(g4, g4)
    e5 = block_diag(g5, -g5)
    
    generators = [e1, e2, e3, e4, e5]
    
    # 1. Check Squares
    print("\nChecking squares e_i^2 = I_8:")
    for i, e in enumerate(generators):
        sq = sp.simplify(e * e)
        if sq == sp.eye(8):
            print(f"e_{i+1}^2 = I (PASS)")
        else:
            print(f"e_{i+1}^2 = \n{sq} (FAIL)")
            return False
            
    # 2. Check Anticommutation
    print("\nChecking anticommutation e_i * e_j = -e_j * e_i:")
    for i in range(5):
        for j in range(i + 1, 5):
            anti_comm = sp.simplify(generators[i] * generators[j] + generators[j] * generators[i])
            if anti_comm == sp.zeros(8, 8):
                print(f"e_{i+1}e_{j+1} + e_{j+1}e_{i+1} = 0 (PASS)")
            else:
                print(f"e_{i+1}e_{j+1} + e_{j+1}e_{i+1} != 0 (FAIL)")
                return False
                
    # 3. Span checking
    print("\nChecking if 32 basis words span M_4(C) x M_4(C) (subspace of 8x8 matrices):")
    # We'll generate all 2^5 = 32 words
    import itertools
    
    basis_words = []
    for k in range(6):
        for indices in itertools.combinations(range(5), k):
            word = sp.eye(8)
            for idx in indices:
                word = word * generators[idx]
            basis_words.append(word)
            
    print(f"Generated {len(basis_words)} basis words.")
    
    # To check spanning of M_4(C) x M_4(C), we note that any block diagonal matrix
    # has 16 + 16 = 32 independent entries.
    # We flatten each 8x8 matrix into a vector of size 64.
    vectors = [sp.flatten(w) for w in basis_words]
    M = sp.Matrix(vectors)
    
    rank = M.rank()
    print(f"Rank of the 32 matrices: {rank}")
    
    if rank == 32:
        print("Cl(5, 0; C) -> M_4(C) x M_4(C) is an exact isomorphism! (PASS)")
        return True
    else:
        print("The matrices do not span M_4(C) x M_4(C). (FAIL)")
        return False

if __name__ == "__main__":
    verify_cl5_complex()
