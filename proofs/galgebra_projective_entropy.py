import sympy as sp
from galgebra.ga import Ga

def main():
    print("--- Formalizing Projective Geometry with GAlgebra ---")

    metric = '0 0 0, 0 1 0, 0 0 1'
    pga, e0, e1, e2 = Ga.build('e0 e1 e2', g=metric)
    
    print("\nAlgebra created:", pga.name)
    
    x1, y1, x2, y2 = sp.symbols('x1 y1 x2 y2', real=True)
    alpha, beta = sp.symbols('alpha beta', real=True)

    p1 = e0 + x1*e1 + y1*e2
    p2 = e0 + x2*e1 + y2*e2
    
    print("\nPoint 1 (normalized):", p1)
    print("Point 2 (normalized):", p2)
    
    ray1 = p1 * alpha
    ray2 = p2 * beta
    
    print("\nRay 1 (unnormalized):", ray1)
    print("Ray 2 (unnormalized):", ray2)
    
    line_normalized = p1 ^ p2
    line_unnormalized = ray1 ^ ray2
    
    print("\nLine connecting Point 1 and Point 2:", line_normalized)
    print("Line connecting Ray 1 and Ray 2:", line_unnormalized)
    
    # Show projective equivalence by comparing scaled normal line to unnormalized line
    diff = line_unnormalized - (line_normalized * (alpha * beta))
    
    is_equivalent = sp.simplify(diff.obj) == 0
    print("\nAre the geometric calculations scale-invariant (projective equivalence)?", is_equivalent)

if __name__ == '__main__':
    main()
