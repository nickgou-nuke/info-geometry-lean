import clifford as cf

def main():
    # Initialize 2D geometric algebra (Clifford algebra Cl(2,0))
    layout, blades = cf.Cl(2)
    e1 = blades['e1']
    e2 = blades['e2']
    e12 = blades['e12']

    def evaluate_orientation(A, B, C):
        """Evaluates the orientation of points A, B, C using 2D GA."""
        # Create vectors from points
        vA = A[0]*e1 + A[1]*e2
        vB = B[0]*e1 + B[1]*e2
        vC = C[0]*e1 + C[1]*e2
        
        # Calculate V1 and V2
        V1 = vB - vA
        V2 = vC - vA
        
        # Outer product
        bivector = V1 ^ V2
        return bivector

    print("=== Geometric Algebra Orientation Evaluation ===")

    # Test case 1: Non-degenerate vertices (Counter-clockwise)
    A1, B1, C1 = (0, 0), (1, 0), (0, 1)
    print("\nTest Case 1: Non-degenerate vertices (CCW)")
    print(f"A={A1}, B={B1}, C={C1}")
    
    biv1 = evaluate_orientation(A1, B1, C1)
    print("V1 ^ V2 =", biv1)
    
    # In clifford Cl(2), the e12 component is stored at index 3 in the multivector array
    e12_coeff1 = biv1.value[3] 
    print(f"Pseudoscalar coefficient (area): {e12_coeff1}")

    # Test case 2: Degenerate vertices (Collinear)
    A2, B2, C2 = (1, 1), (2, 2), (3, 3)
    print("\nTest Case 2: Degenerate vertices (Collinear)")
    print(f"A={A2}, B={B2}, C={C2}")
    
    biv2 = evaluate_orientation(A2, B2, C2)
    print("V1 ^ V2 =", biv2)
    
    e12_coeff2 = biv2.value[3]
    print(f"Pseudoscalar coefficient (area): {e12_coeff2}")

    if abs(e12_coeff2) < 1e-10:
        print("\nResult: The pseudoscalar evaluation strictly yields 0. The points are collinear.")
        print("Conclusion: The system must iterate to the next non-degenerate vertex to establish orientation.")

if __name__ == '__main__':
    main()
