import numpy as np

def cartan_krein_filter(image_patch, epsilon=1e-5):
    """
    Applies the Cartan-Krein filter to a 2x2 image patch of non-negative count data.
    """
    M = np.array(image_patch, dtype=float)
    
    # Cartan Decomposition
    S = (M + M.T) / 2  # Symmetric (Background + Gradients)
    K = (M - M.T) / 2  # Antisymmetric (Circulation/Noise)
    
    # Krein Metric (Determinant)
    det = np.linalg.det(M)
    
    if det > epsilon:
        # V+ (Elliptic/Time-like): Background dominated by Poisson noise
        # Action: Suppress antisymmetric noise, project onto symmetric scalar
        return "V+ (Noise)", S
    elif det < -epsilon:
        # V- (Hyperbolic/Space-like): Gradient/Texture dominated
        # Action: Preserve structural gradients
        return "V- (Texture)", S + 0.5 * K 
    else:
        # Null Space (Parabolic/Light-cone): Exact boundary
        # Action: Extract the null vector orthogonal to the gradient
        eigenvalues, eigenvectors = np.linalg.eig(M)
        null_idx = np.argmin(np.abs(eigenvalues))
        null_vector = eigenvectors[:, null_idx]
        return "Null Space (Contour)", null_vector

# --- Demonstration ---
print("1. Noisy Background Patch (det > 0)")
patch1 = [[10, 12], [8, 11]] # det = 110 - 96 = 14
classification, result = cartan_krein_filter(patch1)
print(f"Classification: {classification}\nFiltered:\n{result}\n")

print("2. Structural Edge Patch (det < 0)")
patch2 = [[20, 2], [2, 0]] # det = 0 - 4 = -4
classification, result = cartan_krein_filter(patch2)
print(f"Classification: {classification}\nFiltered:\n{result}\n")

print("3. Pure Contour Patch (det = 0)")
patch3 = [[10, 5], [2, 1]] # det = 10 - 10 = 0
classification, result = cartan_krein_filter(patch3)
print(f"Classification: {classification}\nNull Vector (Contour Orientation): {result}\n")
