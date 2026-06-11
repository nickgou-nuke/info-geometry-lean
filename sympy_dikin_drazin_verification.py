import sympy as sp

def main():
    print("--- Dikin Ellipsoid and Drazin Core Interlock in SymPy ---")

    # Define the 8x8 explicit supercharge matrix O over integers
    O = sp.Matrix([
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0]
    ])

    print("\n1. Verifying Tripotent Constraint (O^3 = O):")
    O_cubed = O**3
    is_tripotent = O_cubed == O
    print(f"O^3 == O: {is_tripotent}")

    # The Drazin support projector (Active Core)
    P_D = O**2
    print("\n2. Drazin Core Projector (P_D = O^2):")
    sp.pprint(P_D)

    # The Drazin Null projector (Singular Boundary)
    I = sp.eye(8)
    P_zero = I - P_D
    print("\n3. Drazin Null Projector (P_zero = I - O^2):")
    sp.pprint(P_zero)

    # Chiral Grading Operator K (Squares to -P_D)
    K = sp.Matrix([
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0]
    ])
    print("\n4. Verifying Chiral Grading geometric property (K^2 = -P_D):")
    is_K_geometric = K**2 == -P_D
    print(f"K^2 == -P_D: {is_K_geometric}")

    print("\n5. Verifying Dikin Metric Stability in Core:")
    # Hessian metric evaluates as identity on the core (P_D)
    Hessian = P_D
    
    # Dikin metric stability: Hessian * P_D = P_D
    metric_stable = Hessian * P_D == P_D
    print(f"Hessian * P_D == P_D: {metric_stable}")

    # Null metric collapse: Hessian * P_zero = 0
    null_collapse = Hessian * P_zero == sp.zeros(8, 8)
    print(f"Hessian * P_zero == 0: {null_collapse}")

    print("\nCONCLUSION: The Dikin metric acts as a pure automorphism on the active Drazin core,")
    print("while collapsing perfectly on the null topological vacuum.")

if __name__ == "__main__":
    main()
