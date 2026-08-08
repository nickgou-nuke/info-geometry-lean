from clifford import Cl
import math

def main():
    # Initialize 4D Spacetime Algebra (Clifford Algebra Cl(1,3))
    layout, blades = Cl(1, 3)
    e1 = blades['e1']
    e2 = blades['e2']
    e3 = blades['e3']
    e4 = blades['e4']

    # Define causal light-cone operators as idempotents
    # P_+ and P_- act as left and right chiral limit projectors
    # e1*e2 is a bivector that squares to 1 (since e1^2 = 1, e2^2 = -1)
    P_plus = 0.5 * (1 + e1*e2)
    P_minus = 0.5 * (1 - e1*e2)

    print("=== Geometric Algebra Chiral Limits ===")
    print("Left chiral limit projector (P_+):", P_plus)
    print("Right chiral limit projector (P_-):", P_minus)

    # Compute the wedge product of the causal light-cone operators P_+ ^ P_-
    # Since P_+ and P_- are multivectors, their wedge product extracts specific graded parts
    wedge_P = P_plus ^ P_minus
    
    # Compute the geometric product for comparison
    geom_P = P_plus * P_minus

    print("\n=== Topological Vector Potential ===")
    print("Wedge product P_+ ^ P_- (Generates exact topological potential):")
    print(wedge_P)
    print("\nGeometric product P_+ * P_-:")
    print(geom_P)

if __name__ == "__main__":
    main()
