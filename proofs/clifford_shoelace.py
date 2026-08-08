from clifford.g2 import *
import math

def shoelace_orientation(points):
    """
    Computes the oriented area of a simple polygon given as a list of (x,y) points
    using the wedge product in 2D geometric algebra.
    Orientation is positive if counter-clockwise, negative if clockwise.
    """
    if len(points) < 3:
        return 0

    # Convert points to 2D vectors in Clifford GA
    vectors = [p[0]*e1 + p[1]*e2 for p in points]
    
    # Sum the local area bivectors: 1/2 * sum(v_i ^ v_{i+1})
    area_bivector = 0 * e12
    n = len(vectors)
    for i in range(n):
        v1 = vectors[i]
        v2 = vectors[(i + 1) % n]
        
        # Wedge product for 2D vectors gives a bivector proportional to e12
        area_bivector += (v1 ^ v2)
    
    # Divide by 2 as per shoelace formula
    area_bivector = 0.5 * area_bivector
    
    # In Clifford's 2D GA, e12 is at index 3 of the multivector array
    # [scalar, e1, e2, e12]
    area_value = float(area_bivector.value[3])
    
    return area_value

def main():
    # Example 1: CCW square (positive area 4)
    square_ccw = [(0, 0), (2, 0), (2, 2), (0, 2)]
    
    # Example 2: CW square (negative area -4)
    square_cw = [(0, 0), (0, 2), (2, 2), (2, 0)]
    
    # Example 3: CCW triangle
    triangle_ccw = [(0, 0), (3, 0), (0, 4)]
    
    print("=== Geometric Algebra Shoelace Formula ===")
    
    print(f"\nCCW Square points: {square_ccw}")
    print(f"Shoelace Signed Area (GA): {shoelace_orientation(square_ccw)}")
    
    print(f"\nCW Square points: {square_cw}")
    print(f"Shoelace Signed Area (GA): {shoelace_orientation(square_cw)}")
    
    print(f"\nCCW Triangle points: {triangle_ccw}")
    print(f"Shoelace Signed Area (GA): {shoelace_orientation(triangle_ccw)}")

if __name__ == "__main__":
    main()
