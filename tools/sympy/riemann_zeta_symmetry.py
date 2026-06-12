import sympy as sp

def verify_riemann_zeta_functional_equation():
    print("=== Natural Symmetries of the Riemann Zeta Function ===")
    
    s = sp.symbols('s')
    
    # Define the completed zeta function xi(s)
    # xi(s) = pi^(-s/2) * Gamma(s/2) * zeta(s)
    
    def xi(s_val):
        return sp.pi**(-s_val / 2) * sp.gamma(s_val / 2) * sp.zeta(s_val)
    
    # The functional equation states that xi(s) = xi(1 - s)
    xi_s = xi(s)
    xi_1_minus_s = xi(1 - s)
    
    print("\nCompleted Riemann Zeta Function xi(s):")
    print(xi_s)
    
    print("\nReflected Completed Zeta Function xi(1 - s):")
    print(xi_1_minus_s)
    
    print("\nFunctional Equation: xi(s) == xi(1 - s)")
    
    # Let's verify it numerically at a few points to demonstrate the symmetry
    test_points = [0.5 + 14.134725j, 2, 3, 0.5 + 21.022040j] # First two non-trivial zeros and some integers
    
    print("\nNumerical Verification:")
    for pt in test_points:
        val1 = xi(pt).evalf(10)
        val2 = xi(1 - pt).evalf(10)
        
        # Format the output for readability
        val1_str = str(val1).replace('I', 'j')
        val2_str = str(val2).replace('I', 'j')
        print(f"s = {pt}:")
        print(f"  xi(s)     = {val1_str}")
        print(f"  xi(1 - s) = {val2_str}")
        
        # Check if they are numerically close
        diff = abs(val1 - val2)
        print(f"  Difference  = {diff:.2e}")

if __name__ == "__main__":
    verify_riemann_zeta_functional_equation()
