from sympy import symbols
from galgebra.ga import Ga
from galgebra.printer import Format

def main():
    # Format()
    print("Formalizing Hestenes' Krein Formulation and Clifford-Jordan-Lie Split in STA")
    
    # Spacetime Algebra (STA) signature: (1, -1, -1, -1) which relates to Krein space forms
    sta = Ga('e_0 e_1 e_2 e_3', g=[1, -1, -1, -1])
    e0, e1, e2, e3 = sta.mv()

    # Create two arbitrary multivectors (vectors in this case)
    a = sta.mv('a', 'vector')
    b = sta.mv('b', 'vector')

    # Full Geometric Product
    ab = a * b

    # Symmetric Jordan Product (Metric / Inner Product for vectors)
    # ab + ba = 2 (a \cdot b)
    jordan = (a * b + b * a) / 2

    # Anti-symmetric Lie Commutator (Symplectic / Wedge Product for vectors)
    # ab - ba = 2 (a \wedge b)
    lie = (a * b - b * a) / 2

    print("\n--- Geometric Product a*b ---")
    print(ab)
    
    print("\n--- Symmetric Jordan Product (a*b + b*a)/2 ---")
    print(jordan)
    
    print("\n--- Anti-symmetric Lie Commutator (a*b - b*a)/2 ---")
    print(lie)
    
    print("\n--- Verification of the Split: ab == jordan + lie ---")
    print(ab == jordan + lie)

if __name__ == "__main__":
    main()
