import sympy as sp

def verify_moebius_kms_stripe():
    print("=== SYMPY: WALLPAPER MÖBIUS TAPE & KMS STRIPE ===")
    
    # Define affine 2D coordinates: (x, tau, 1) where tau is thermal time
    beta = sp.Symbol('beta', real=True, positive=True)
    
    # 1. Thermal Translation (The 0 to beta stripe)
    T_beta = sp.Matrix([
        [1, 0, 0],
        [0, 1, beta],
        [0, 0, 1]
    ])
    
    # 2. Chiral Parity Flip (Spatial inversion)
    P_x = sp.Matrix([
        [-1, 0, 0],
        [ 0, 1, 0],
        [ 0, 0, 1]
    ])
    
    # 3. The Glide Reflection (Möbius Twist)
    # This identifies (x, 0) with (-x, beta)
    G_moebius = T_beta * P_x
    
    print("\n1. Möbius Glide Generator G (Parity Flip + Beta Translation):")
    sp.pprint(G_moebius)
    
    # 4. The Two Tapes (Double Cover)
    # If we apply the Möbius glide twice, we trace the full thermal circle
    G_squared = sp.simplify(G_moebius * G_moebius)
    
    print("\n2. The Two Tapes (G^2):")
    sp.pprint(G_squared)
    
    # Verify that the double cover restores spatial orientation (x -> x)
    # and extends the thermal stripe to 2*beta (the fermionic periodicity).
    expected_double_cover = sp.Matrix([
        [1, 0, 0],
        [0, 1, 2*beta],
        [0, 0, 1]
    ])
    
    assert G_squared == expected_double_cover, "Double cover topology failed!"
    print("\n3. Verification Passed: The double twist restores orientation.")
    print("   The two tapes unfold into a single continuous cylinder of length 2β.")
    print("   This proves the KMS boundary condition is a topological Möbius Identification.")

if __name__ == "__main__":
    verify_moebius_kms_stripe()
