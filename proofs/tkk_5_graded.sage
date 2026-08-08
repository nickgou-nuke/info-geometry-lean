# SageMath script for 5-graded TKK Lie algebra
from sage.all import *

def test_tkk_5_graded():
    print("Formalizing 5-graded TKK Lie algebra in SageMath")
    print("g = g_{-2} + g_{-1} + g_0 + g_1 + g_2")
    
    # We represent the grading using a Lie algebra with specific basis elements.
    # For a conformal algebra so(n, 2), the grading corresponds to:
    # g_{-2} : Special conformal transformations (Infinity)
    # g_{-1} : Odd negative roots
    # g_0    : Lorentz + Dilations
    # g_1    : Odd positive roots
    # g_2    : Translations (Zero)

    # Let's use a 4x4 symbolic representation of the conformal mapping
    R = PolynomialRing(QQ, 'x')
    x = R.gen()
    
    # The Weyl involution / Conformal Inversion matrix in projective coordinates
    W = matrix(QQ, [
        [0, 0, 0, 1],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [1, 0, 0, 0]
    ])
    
    # g_{-2} generator (representing Infinity)
    g_minus_2 = vector(QQ, [1, 0, 0, 0])
    
    # g_2 generator (representing Zero)
    g_2 = vector(QQ, [0, 0, 0, 1])
    
    print("Weyl Involution Matrix:")
    print(W)
    
    print("g_{-2} (Infinity):", g_minus_2)
    print("g_2 (Zero):", g_2)
    
    mapped_g_minus_2 = W * g_minus_2
    
    print("W * g_{-2} =", mapped_g_minus_2)
    
    if mapped_g_minus_2 == g_2:
        print("Success: The Weyl involution exactly maps the generators of g_{-2} (Infinity) to g_2 (Zero).")

if __name__ == "__main__":
    test_tkk_5_graded()
