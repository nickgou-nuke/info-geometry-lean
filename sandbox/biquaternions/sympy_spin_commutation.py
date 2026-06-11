import sympy as sp

def verify_spin_commutation():
    print("--- SymPy Verification of Spin Operators in Complexified Clifford Algebra ---")
    
    # Define standard Pauli matrices
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    
    hbar = sp.Symbol('hbar', real=True)
    
    # Based on the even subalgebra isomorphism phi_C: Cl+(3,0; C) -> M2(C)
    # phi_C(e2e3) = -i*sigma1
    # phi_C(e3e1) = -i*sigma2
    # phi_C(e1e2) = -i*sigma3
    
    B1 = -sp.I * sigma1
    B2 = -sp.I * sigma2
    B3 = -sp.I * sigma3
    
    # Define the Spin operators as scaled bivectors
    S1_geom = (hbar / 2) * B1
    S2_geom = (hbar / 2) * B2
    S3_geom = (hbar / 2) * B3
    
    # Calculate geometric commutator
    comm_geom = S1_geom * S2_geom - S2_geom * S1_geom
    
    print("\n1. Geometric Bivector Commutator [S1, S2]:")
    sp.pprint(comm_geom)
    
    # Compare with \hbar * S3
    expected_geom = hbar * S3_geom
    print("\nExpected hbar * S3_geom:")
    sp.pprint(expected_geom)
    
    if comm_geom == expected_geom:
        print("SUCCESS: [S1, S2] = \hbar S3 exactly holds in the geometric basis.")
    else:
        print("FAILED geometric relation.")
        
    # Contrast with standard Quantum Mechanics operators
    S1_qm = (hbar / 2) * sigma1
    S2_qm = (hbar / 2) * sigma2
    S3_qm = (hbar / 2) * sigma3
    
    comm_qm = S1_qm * S2_qm - S2_qm * S1_qm
    expected_qm = sp.I * hbar * S3_qm
    
    print("\n2. Quantum Mechanical Pauli Commutator [S1, S2]:")
    if comm_qm == expected_qm:
        print("SUCCESS: [S1, S2] = i\hbar S3 exactly holds in the standard QM basis.")
        
    print("\nCONCLUSION:")
    print("The geometric algebra commutator naturally yields \hbar S3.")
    print("The 'i' in the standard QM commutation relation arises precisely from")
    print("mapping the bivector operators to the complex Pauli matrices without the -i phase.")

if __name__ == "__main__":
    verify_spin_commutation()
