import numpy as np

def analyze_structure_tensor(Ix, Iy, weights=None, epsilon=1e-8):
    """
    Computes the Structure Tensor J = sum w_p * (grad_p @ grad_p.T)
    and evaluates the rigorous feature map rho(J).
    
    Ix, Iy: Arrays of local image gradients
    """
    Ix = np.array(Ix).flatten()
    Iy = np.array(Iy).flatten()
    
    if weights is None:
        weights = np.ones_like(Ix)
        
    # Construct J = [ [sum(w Ix^2), sum(w Ix Iy)], [sum(w Ix Iy), sum(w Iy^2)] ]
    J_00 = np.sum(weights * Ix**2)
    J_01 = np.sum(weights * Ix * Iy)
    J_11 = np.sum(weights * Iy**2)
    
    J = np.array([[J_00, J_01],
                  [J_01, J_11]])
    
    # Trace and Determinant
    tr_J = np.trace(J)
    det_J = np.linalg.det(J)
    
    # Normalized Degeneracy Score (rho)
    # rho -> 0: Rank-1 edge
    # rho -> 1: Isotropic texture/corner
    rho = (4 * det_J) / (tr_J**2 + epsilon)
    
    # Singular vectors (approximate kernel space)
    U, S, Vt = np.linalg.svd(J)
    
    print(f"J Trace: {tr_J:.2f}")
    print(f"J Det:   {det_J:.2f}")
    print(f"rho(J):  {rho:.4f}")
    
    if tr_J < epsilon:
        print("Classification: Flat region (J = 0)")
    elif rho < 0.1:
        print("Classification: 1D Dominant Edge (Rank 1 / Null Cone)")
        print(f"Normal vector (Edge direction): {Vt[1]}")
    else:
        print("Classification: 2D Texture / Corner (Rank 2)")

# --- Tests ---
print("--- 1. Flat Background ---")
# Ix = Iy = 0 everywhere
analyze_structure_tensor([0,0,0], [0,0,0])

print("\n--- 2. Pure 1D Edge (Collinear Gradients) ---")
# Gradient is strictly along the x-axis (Ix > 0, Iy = 0)
analyze_structure_tensor([10, 5, 20], [0, 0, 0])

print("\n--- 3. Isotropic Texture / Corner ---")
# Gradients exist in both orthogonal directions equally
analyze_structure_tensor([10, 0, -10, 0], [0, 10, 0, -10])
