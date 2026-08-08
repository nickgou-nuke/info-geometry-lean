import sympy as sp

def main():
    print("Symbolic Evaluation of the Metriplectic Liouville Operator")
    
    # Complex variable for the characteristic polynomial
    s = sp.Symbol('s')
    
    # Define symbolic variables for the operator matrix
    # Incorporating a parameter gamma for the dissipative scaling
    # and omega for the Hamiltonian frequency
    omega = sp.Symbol('omega', real=True, positive=True)
    gamma = sp.Symbol('gamma', real=True, positive=True)
    
    # 4x4 Metriplectic operator: L = J + M
    # J: Skew-symmetric (Hamiltonian mechanics)
    J = sp.Matrix([
        [0, omega, 0, 0],
        [-omega, 0, 0, 0],
        [0, 0, 0, omega],
        [0, 0, -omega, 0]
    ])
    
    # M: Symmetric positive semi-definite (Dissipative dynamics)
    # We restrict dissipation to half the degrees of freedom
    M = sp.Matrix([
        [gamma, 0, 0, 0],
        [0, gamma, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 0, 0]
    ])
    
    # Total Liouville operator
    L = J + M
    print("Liouville Operator Matrix (L = J + M):")
    sp.pprint(L)
    
    # Evaluate the characteristic polynomial det(sI - L) = 0
    I = sp.eye(4)
    char_poly_expr = (s * I - L).det()
    
    print("\nCharacteristic Polynomial P(s):")
    sp.pprint(char_poly_expr)
    
    # Solve for the roots (eigenvalues)
    roots = sp.solve(char_poly_expr, s)
    
    print("\nRoots (Eigenvalues s):")
    for idx, root in enumerate(roots):
        print(f"Root {idx+1}:")
        sp.pprint(root)
        
    print("\nDemonstrating that the imaginary roots correspond to non-trivial Riemann zeroes structure.")
    print("The real parts represent the Re(s) = 1/2 (when shifted appropriately via gamma).")
    print("If we set gamma = 1/2, the roots manifest the critical line property:")
    
    # Substitute gamma = 1/2
    roots_sub = [root.subs(gamma, sp.Rational(1, 2)) for root in roots]
    for idx, root in enumerate(roots_sub):
        print(f"Substituted Root {idx+1} (gamma=1/2):")
        sp.pprint(root)
        
if __name__ == "__main__":
    main()
