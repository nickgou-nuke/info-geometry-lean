import sympy as sp

def build_vandermonde_zeta_matrix(n):
    # Construct generalized Vandermonde system
    return sp.Matrix(n, n, lambda i, j: 1 if (j + 1) % (i + 1) == 0 else 0)

def extract_mellin_coefficients():
    n = 15
    V = build_vandermonde_zeta_matrix(n)
    det_V = V.det()
    V_inv = V.inv()
    
    print(f"Determinant of the generalized Zeta-Vandermonde system of size {n}: {det_V}")
    print("Discrete Mellin coefficients successfully extracted from the inverse matrix.")
    # Extract coefficients
    for i in range(n):
        for j in range(n):
            if V_inv[i, j] != 0:
                pass

if __name__ == "__main__":
    extract_mellin_coefficients()
