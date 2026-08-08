import sympy as sp
from galgebra.ga import Ga

def main():
    # Setup 2D Geometric Algebra
    ga = Ga('e_1 e_2')
    e1, e2 = ga.mv()
    
    # Define three consecutive vertices as symbols
    x1, y1, x2, y2, x3, y3 = sp.symbols('x1 y1 x2 y2 x3 y3')
    
    # Vertices
    v1 = x1*e1 + y1*e2
    v2 = x2*e1 + y2*e2
    v3 = x3*e1 + y3*e2
    
    # Edge vectors
    u = v2 - v1
    v = v3 - v2
    
    # Outer product (area bivector)
    area_bivector = u ^ v
    
    # Orientation matrix determinant
    # Matrix is:
    # [ 1, x1, y1 ]
    # [ 1, x2, y2 ]
    # [ 1, x3, y3 ]
    det = sp.Matrix([
        [1, x1, y1],
        [1, x2, y2],
        [1, x3, y3]
    ]).det()
    
    print("Area Bivector (u ^ v):")
    print(area_bivector)
    print("\nOrientation Matrix Determinant:")
    print(sp.simplify(det))

if __name__ == "__main__":
    main()
