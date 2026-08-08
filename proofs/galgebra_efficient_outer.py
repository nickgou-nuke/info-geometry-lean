import sympy as sp
from galgebra.ga import Ga

def main():
    # Setup 2D geometric algebra
    coords = sp.symbols('x y', real=True)
    ga2d = Ga('e', g=[1, 1], coords=coords)
    e_x, e_y = ga2d.mv()

    # Define coordinates for points A, B, C
    Ax, Ay = sp.symbols('A_x A_y', real=True)
    Bx, By = sp.symbols('B_x B_y', real=True)
    Cx, Cy = sp.symbols('C_x C_y', real=True)

    # Define vectors for points A, B, C
    A = Ax * e_x + Ay * e_y
    B = Bx * e_x + By * e_y
    C = Cx * e_x + Cy * e_y

    # Define V1 and V2
    V1 = B - A
    V2 = C - A

    print("Vector V1 (B - A):", V1)
    print("Vector V2 (C - A):", V2)

    # Calculate outer product (bivector)
    bivector_area = V1 ^ V2

    print("\nOuter Product V1 ^ V2:")
    print(bivector_area)

    # The efficient determinant formula
    efficient_det = (Bx - Ax)*(Cy - Ay) - (By - Ay)*(Cx - Ax)
    print("\nEfficient Determinant Formula:")
    print(efficient_det)

    # In GAlgebra, we can check equality by checking if the difference simplifies to zero
    diff = sp.simplify((bivector_area - efficient_det * (e_x ^ e_y)).obj)
    print("\nDifference between outer product and efficient determinant:", diff)
    
    if diff == 0:
        print("Success: The outer product V1 ^ V2 identically yields the efficient determinant formula.")
    else:
        print("Failure: They do not match.")

if __name__ == '__main__':
    main()
