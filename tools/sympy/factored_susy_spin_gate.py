import sympy as sp

def verify_factored_layers():
    print("=== OMEGA AUTOMATH: FACTORED LAYERS DIAGNOSTIC ===")
    
    # 1. Factored Spin-1/2 Layer Definition
    # J_zero = (1/2)*sigma_z, J_plus = sigma_x + i*sigma_y, J_minus = sigma_x - i*sigma_y
    J_zero  = sp.Matrix([[1/2, 0], [0, -1/2]])
    J_plus  = sp.Matrix([[0, 1], [0, 0]])
    J_minus = sp.Matrix([[0, 0], [1, 0]])
    
    assert J_zero * J_plus - J_plus * J_zero == J_plus, "Factored SU(2) J+ commutation failed"
    assert J_plus * J_minus - J_minus * J_plus == 2 * J_zero, "Factored SU(2) J0 commutation failed"
    print("[SUCCESS] Layer 1: Finite Spin Algebra invariants cleanly decoupled.")
    
    # 2. Factored SUSY Block Definition
    A = J_minus
    A_dag = J_plus
    H_minus = A_dag * A
    H_plus = A * A_dag
    
    assert A * H_minus == H_plus * A, "Factored SUSY Hamiltonian mirroring failed"
    print("[SUCCESS] Layer 2: Finite SUSY Supergraded Block invariants cleanly decoupled.")
    print("\n[COMPLETE] Global multi-system hygiene factoring passed.")

if __name__ == '__main__':
    verify_factored_layers()
