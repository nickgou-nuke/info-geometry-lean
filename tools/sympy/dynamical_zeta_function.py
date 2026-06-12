import sympy as sp

def verify_matrix_zeta_identity():
    print("=== Dynamical Zeta Functions (Baladi) ===")
    print("Verifying Exercise 0: det(I - zL) = exp(-sum_n z^n/n Tr(L^n))")
    
    # We'll verify it up to order 3 for a general 2x2 matrix
    z = sp.Symbol('z')
    l11, l12, l21, l22 = sp.symbols('l11 l12 l21 l22')
    L = sp.Matrix([[l11, l12], [l21, l22]])
    I = sp.eye(2)
    
    # Left hand side
    det_lhs = (I - z * L).det()
    print("\nLHS: det(I - zL) =")
    print(det_lhs)
    
    # Right hand side taylor expansion of log(det)
    # log(det(I - zL)) = - sum_{n=1}^infty (z^n / n) Tr(L^n)
    tr1 = sp.trace(L)
    tr2 = sp.trace(L**2)
    tr3 = sp.trace(L**3)
    
    log_det_rhs_expansion = - z * tr1 - (z**2 / 2) * tr2 - (z**3 / 3) * tr3
    
    # Expand LHS log(det) up to O(z^4)
    # det_lhs = 1 - z * tr(L) + z^2 * det(L)
    log_lhs_expansion = sp.series(sp.log(det_lhs), z, 0, 4).removeO()
    
    print("\nTaylor expansion of log(det(I - zL)) up to z^3:")
    print(log_lhs_expansion)
    
    print("\nRHS expansion - sum (z^n / n) Tr(L^n) up to z^3:")
    print(log_det_rhs_expansion)
    
    diff = sp.simplify(log_lhs_expansion - log_det_rhs_expansion)
    print(f"\nDifference: {diff}")
    print(f"Match: {diff == 0}")

if __name__ == "__main__":
    verify_matrix_zeta_identity()
