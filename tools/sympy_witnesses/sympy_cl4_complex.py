import sympy as sp
from sympy.physics.quantum import TensorProduct

def verify_cl4_complex():
    print("--- Verifying Cl(4,0; C) -> M_4(C) Isomorphism ---")
    
    # Pauli matrices
    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    
    # Generators
    e1 = TensorProduct(s1, I2)
    e2 = TensorProduct(s2, I2)
    e3 = TensorProduct(s3, s1)
    e4 = TensorProduct(s3, s2)
    
    generators = [e1, e2, e3, e4]
    
    # 1. Check Squares
    print("\nChecking squares e_i^2 = I:")
    for i, e in enumerate(generators):
        sq = sp.simplify(e * e)
        if sq == sp.eye(4):
            print(f"e_{i+1}^2 = I (PASS)")
        else:
            print(f"e_{i+1}^2 = \n{sq} (FAIL)")
            return False
            
    # 2. Check Anticommutation
    print("\nChecking anticommutation e_i * e_j = -e_j * e_i:")
    for i in range(4):
        for j in range(i + 1, 4):
            anti_comm = sp.simplify(generators[i] * generators[j] + generators[j] * generators[i])
            if anti_comm == sp.zeros(4, 4):
                print(f"e_{i+1}e_{j+1} + e_{j+1}e_{i+1} = 0 (PASS)")
            else:
                print(f"e_{i+1}e_{j+1} + e_{j+1}e_{i+1} != 0 (FAIL)")
                return False
                
    # 3. Span checking
    # Cl(4) has 16 basis words. We will generate all of them and check if they are linearly independent.
    print("\nChecking if 16 basis words span M_4(C):")
    basis_words = [
        sp.eye(4),
        e1, e2, e3, e4,
        e1*e2, e1*e3, e1*e4, e2*e3, e2*e4, e3*e4,
        e1*e2*e3, e1*e2*e4, e1*e3*e4, e2*e3*e4,
        e1*e2*e3*e4
    ]
    
    # Flatten matrices into 16-dimensional vectors
    vectors = [sp.flatten(w) for w in basis_words]
    M = sp.Matrix(vectors)
    
    # Calculate rank
    rank = M.rank()
    print(f"Rank of the 16 matrices: {rank}")
    
    if rank == 16:
        print("Cl(4, 0; C) -> M_4(C) is an exact isomorphism! (PASS)")
        return True
    else:
        print("The matrices do not span M_4(C). (FAIL)")
        return False

if __name__ == "__main__":
    verify_cl4_complex()
