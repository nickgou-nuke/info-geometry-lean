# log_determinant_homomorphism.sage

def test_log_det_homomorphism(n=3):
    # Create random matrices over a real field
    R = RealField()
    A = random_matrix(R, n)
    B = random_matrix(R, n)

    # Ensure they are invertible
    while not A.is_invertible():
        A = random_matrix(R, n)
    while not B.is_invertible():
        B = random_matrix(R, n)

    # Tensor Product (Kronecker product)
    T = A.tensor_product(B)
    
    # Direct Sum (Block diagonal)
    D = block_diagonal_matrix([A, B])

    # Determinant properties
    det_A = A.det()
    det_B = B.det()
    det_T = T.det()
    det_D = D.det()

    print("det(A):", det_A)
    print("det(B):", det_B)
    print("det(A tensor B) expected det(A)^n * det(B)^n:", det_A^n * det_B^n)
    print("det(A tensor B) actual:", det_T)
    print("det(A direct sum B) expected det(A) * det(B):", det_A * det_B)
    print("det(A direct sum B) actual:", det_D)

    # Logarithmic determinant additivity for direct sum
    # Let's square the matrices to guarantee positive determinant for real log
    A2 = A * A.transpose()
    B2 = B * B.transpose()
    D2 = block_diagonal_matrix([A2, B2])

    log_det_A2 = log(A2.det())
    log_det_B2 = log(B2.det())
    log_det_D2 = log(D2.det())

    print("\nAdditivity of negative log determinant for Direct Sum:")
    print("-log(det(A2 direct sum B2)):", -log_det_D2)
    print("-log(det(A2)) + -log(det(B2)):", -log_det_A2 - log_det_B2)

test_log_det_homomorphism()
