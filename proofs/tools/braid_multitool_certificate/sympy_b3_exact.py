import sympy as sp

def run_b3_yang_baxter_certificate():
    print("=======================================")
    print(" B3 YANG-BAXTER SYMPY EXACT CERTIFICATE")
    print("=======================================")
    
    # Define exact symbolic parameters
    q = sp.Symbol('q', nonzero=True)
    
    # Braid Group B3 Burau Representation (reduced 2x2)
    # R1 = sigma_1, R2 = sigma_2
    R1 = sp.Matrix([
        [-q, 1],
        [ 0, 1]
    ])
    
    R2 = sp.Matrix([
        [1,  0],
        [q, -q]
    ])
    
    print("\n1. Exact Rational Generators for B3 (Reduced Burau):")
    print("R1 (sigma_1):")
    sp.pprint(R1)
    print("\nR2 (sigma_2):")
    sp.pprint(R2)
    
    # Compute the Yang-Baxter relation: R1 * R2 * R1 == R2 * R1 * R2
    LHS = R1 * R2 * R1
    RHS = R2 * R1 * R2
    
    print("\n2. Checking Artin / Yang-Baxter Braid Relation:")
    print("LHS = R1 * R2 * R1:")
    sp.pprint(sp.simplify(LHS))
    print("\nRHS = R2 * R1 * R2:")
    sp.pprint(sp.simplify(RHS))
    
    difference = sp.simplify(LHS - RHS)
    is_exact = difference == sp.zeros(2, 2)
    
    print(f"\n[CERTIFICATE] Yang-Baxter relation exactly verified: {is_exact}")
    
    if is_exact:
        print("Certificate: LHS and RHS are exact algebraic equivalents over Q(q).")

if __name__ == "__main__":
    run_b3_yang_baxter_certificate()
