# SageMath Script for Local Concavity and Orientation Matrix

def analyze_vertices(p1, p2, p3, global_orientation='CCW'):
    """
    Computes the orientation matrix determinant for 3 consecutive vertices.
    p1, p2, p3 are tuples (x, y)
    global_orientation is either 'CCW' (counter-clockwise) or 'CW' (clockwise)
    """
    M = Matrix([
        [p1[0], p1[1], 1],
        [p2[0], p2[1], 1],
        [p3[0], p3[1], 1]
    ])
    
    det_M = M.determinant()
    
    if det_M == 0:
        return "collinear"
    
    if global_orientation == 'CCW':
        if det_M > 0:
            return "convex"
        else:
            return "concave"
    elif global_orientation == 'CW':
        if det_M < 0:
            return "convex"
        else:
            return "concave"
    else:
        raise ValueError("Unknown global orientation")

# Example usage
p1 = (0, 0)
p2 = (2, 0)
p3 = (1, 1)

print(f"Vertices: {p1}, {p2}, {p3}")
print(f"Orientation Matrix:\n{Matrix([[p1[0], p1[1], 1], [p2[0], p2[1], 1], [p3[0], p3[1], 1]])}")
print(f"Determinant: {Matrix([[p1[0], p1[1], 1], [p2[0], p2[1], 1], [p3[0], p3[1], 1]]).determinant()}")
print(f"Result (CCW): {analyze_vertices(p1, p2, p3, 'CCW')}")
