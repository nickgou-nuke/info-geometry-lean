import sympy as sp

def verify_twisted_hecke_algebra_representation():
    print("=== Twisted Hecke Algebra and Klein Bottle (Aubert-Plymen) ===")
    
    # Define symbolic parameters w and z for the character
    w, z = sp.symbols('w z')
    
    # 2D representation matrices
    Y = sp.Matrix([[w, 0], [0, -w]])
    s = sp.Matrix([[0, 1], [1, 0]])
    X = sp.Matrix([[z, 0], [0, 1/z]])
    
    print("\nTwisted Group Algebra Generators:")
    print("Y =\n", Y)
    print("s =\n", s)
    print("X =\n", X)
    
    # Verify relations:
    # 1. s^2 = 1
    # 2. sX = X^(-1)s
    # 3. sY = -Ys
    # 4. XY = YX
    
    rel1 = sp.simplify(s**2 - sp.eye(2))
    print("\nRelation 1: s^2 == I ->", rel1 == sp.zeros(2))
    
    rel2_lhs = s * X
    rel2_rhs = X.inv() * s
    print("Relation 2: sX == X^(-1)s ->", sp.simplify(rel2_lhs - rel2_rhs) == sp.zeros(2))
    
    rel3_lhs = s * Y
    rel3_rhs = -Y * s
    print("Relation 3: sY == -Ys ->", sp.simplify(rel3_lhs - rel3_rhs) == sp.zeros(2))
    
    rel4_lhs = X * Y
    rel4_rhs = Y * X
    print("Relation 4: XY == YX ->", sp.simplify(rel4_lhs - rel4_rhs) == sp.zeros(2))
    
    print("\nTopology of the parameter space:")
    print("The isomorphism relation (conjugation by s) sends (w, z) to (-w, z^(-1)).")
    print("On the unitary locus |w| = |z| = 1, this free orientation-reversing involution")
    print("yields a quotient homeomorphic to a Klein bottle.")

if __name__ == "__main__":
    verify_twisted_hecke_algebra_representation()
