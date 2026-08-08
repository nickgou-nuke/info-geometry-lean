from sympy import symbols, Matrix, simplify
from galgebra.ga import Ga

def main():
    # Setup 2D geometric algebra
    coords = symbols('x y')
    ga = Ga('e', g=[1, 1], coords=coords)
    e1, e2 = ga.mv()
    
    # Points
    Ax, Ay, Bx, By, Cx, Cy = symbols('A_x A_y B_x B_y C_x C_y')
    
    # 1. Orientation Matrix Determinant (Cofactor Expansion)
    M = Matrix([
        [1, Ax, Ay],
        [1, Bx, By],
        [1, Cx, Cy]
    ])
    det_M = simplify(M.det())
    
    print("=== Orientation Matrix Determinant ===")
    print(det_M)
    
    # 2. Geometric Algebra cross product (bivector) of BA and BC
    # BA = A - B
    # BC = C - B
    BA = (Ax - Bx)*e1 + (Ay - By)*e2
    BC = (Cx - Bx)*e1 + (Cy - By)*e2
    
    # Wedge product represents the signed area
    bivector = BA ^ BC
    
    print("\n=== Bivector of BA ^ BC ===")
    print(bivector)
    
    # Extract the scalar coefficient of the e_x^e_y bivector part
    bivector_mag = simplify(bivector.get_coefs(2)[0]) # getting the symbolic coefficient of the bivector
    
    print("\n=== Magnitude of Bivector (coefficient) ===")
    print(bivector_mag)
    
    # Show that Det = - (BA ^ BC)
    # The geometric difference is a sign convention (det defines ABC orientation, BA^BC defines B as origin)
    # If we evaluated AB ^ AC, it would be strictly equal to the determinant.
    print("\n=== Geometric Equivalence Check ===")
    diff = simplify(det_M + bivector_mag)
    print("Difference between Determinant and -Bivector_Magnitude (should be 0):")
    print(diff)
    
    # For completeness, let's also show AB ^ AC matches the determinant directly
    AB = (Bx - Ax)*e1 + (By - Ay)*e2
    AC = (Cx - Ax)*e1 + (Cy - Ay)*e2
    bivector_A = AB ^ AC
    bivector_A_mag = simplify(bivector_A.get_coefs(2)[0])
    
    print("\n=== Equivalence of Det and AB ^ AC ===")
    print("Difference:", simplify(det_M - bivector_A_mag))


if __name__ == "__main__":
    main()
