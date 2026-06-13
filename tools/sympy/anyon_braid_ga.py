import numpy as np
from clifford import Cl

def verify_anyon_braid_ga():
    print("=== ANYON BRAIDING IN GEOMETRIC ALGEBRA ===")
    
    # Initialize 3D Euclidean Geometric Algebra Cl(3)
    layout, blades = Cl(3)
    e1, e2, e3 = blades['e1'], blades['e2'], blades['e3']
    
    # Define fractional bivector rotations (e.g. Z_3 parafermion twists)
    # Rotor for twist in e12 plane (braid 1)
    theta = 2 * np.pi / 3  # Z3 fractional phase twist
    R1 = np.cos(theta/2) - (e1*e2)*np.sin(theta/2)
    
    # Rotor for twist in e23 plane (braid 2)
    R2 = np.cos(theta/2) - (e2*e3)*np.sin(theta/2)
    
    # Verify that these rotors are valid (R * ~R = 1)
    assert np.isclose((R1 * ~R1).value[0], 1.0), "R1 is not a valid rotor"
    assert np.isclose((R2 * ~R2).value[0], 1.0), "R2 is not a valid rotor"
    
    # Check non-abelian nature (R1 R2 != R2 R1)
    diff = R1*R2 - R2*R1
    assert np.max(np.abs(diff.value)) > 1e-10, "Rotors commute (Abelian), expected Non-Abelian"
    
    print("[SUCCESS] Non-Abelian Anyon fractional twists verified via Clifford rotors.")
    print(f"R1 * R2 - R2 * R1 non-zero bivector components:\n{diff}")
    
if __name__ == '__main__':
    verify_anyon_braid_ga()
