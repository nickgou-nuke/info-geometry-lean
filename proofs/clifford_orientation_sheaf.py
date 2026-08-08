import clifford as cf
import numpy as np

def main():
    print("=== Clifford: Orientation Sheaf Sections ===")
    # Spacetime Algebra (STA) Cl(1, 3)
    layout, blades = cf.Cl(1, 3)
    e0 = blades['e1']  # timelike
    e1 = blades['e2']  # spacelike
    e2 = blades['e3']
    e3 = blades['e4']
    
    I_space = e1 ^ e2 ^ e3
    I_time = e0
    
    print("\nSpacetime Algebra Cl(1, 3)")
    print("e0**2 =", e0**2)
    print("e1**2 =", e1**2)
    
    # Define a rotor for a spatial rotation (e.g., in e1-e2 plane)
    theta = np.pi / 4
    R_rot = np.cos(theta/2) - np.sin(theta/2) * (e1 ^ e2)
    
    # Define a rotor for a Lorentz boost (e.g., in e0-e1 plane)
    phi = 0.5 # rapidity
    R_boost = np.cosh(phi/2) + np.sinh(phi/2) * (e0 ^ e1)
    
    def apply_transformation(R, blade):
        return R * blade * (~R)
        
    def apply_reflection(v, n):
        return -n * v * n.inv()
        
    def P_transform(v):
        return apply_reflection(apply_reflection(apply_reflection(v, e1), e2), e3)
        
    def T_transform(v):
        return apply_reflection(v, e0)
    
    print("\n--- Modeling Associated Bundle Sections O(M) x_sigma {-1, +1} ---")
    
    print("\n1. Proper Orthochronous Transformation (Spatial Rotation in e1-e2 plane):")
    rot_time = apply_transformation(R_rot, I_time)
    # The space pseudoscalar transforms slightly differently since we are rotating the basis vectors
    rot_space = apply_transformation(R_rot, e1) ^ apply_transformation(R_rot, e2) ^ apply_transformation(R_rot, e3)
    print("  I_time transformed:", np.round(rot_time.value, 4) if hasattr(rot_time, 'value') else rot_time)
    print("  I_space transformed:", np.round(rot_space.value, 4) if hasattr(rot_space, 'value') else rot_space)
    
    print("\n2. Spatial Inversion (P) - Improper Orthochronous:")
    P_time = P_transform(e0)
    P_space = P_transform(e1) ^ P_transform(e2) ^ P_transform(e3)
    print("  Transformed e0 (Time Pseudoscalar):", P_time)
    print("  Transformed I_space (Space Pseudoscalar):", P_space)
    
    # Identifying sections
    sigma_minus_P = 1 if P_time == e0 else -1
    sigma_plus_P = 1 if P_space == I_space else -1
    print(f"  -> Section evaluated on P: sigma_+ = {sigma_plus_P}, sigma_- = {sigma_minus_P}")
    
    print("\n3. Time Inversion (T) - Improper Non-Orthochronous:")
    T_time = T_transform(e0)
    T_space = T_transform(e1) ^ T_transform(e2) ^ T_transform(e3)
    print("  Transformed e0 (Time Pseudoscalar):", T_time)
    print("  Transformed I_space (Space Pseudoscalar):", T_space)
    
    sigma_minus_T = 1 if T_time == e0 else -1
    sigma_plus_T = 1 if T_space == I_space else -1
    print(f"  -> Section evaluated on T: sigma_+ = {sigma_plus_T}, sigma_- = {sigma_minus_T}")

if __name__ == "__main__":
    main()
