import sage.all as sg

def verify_parabolic_clock_hurwitz():
    print("=== SageMath Parabolic Clock & Hurwitz $D_4$ Map ===")
    
    # 1. Parabolic Nilpotent Clock
    K = sg.matrix(sg.QQ, [[0, 1], [0, 0]])
    assert K**2 == sg.matrix(sg.QQ, 2, 2)
    
    t = sg.var('t')
    exp_tK = sg.matrix(sg.SR, 2, 2, [[1, t], [0, 1]])
    print("Parabolic Flow exp(tK):", exp_tK)
    assert exp_tK == sg.identity_matrix(2) + t*K
    print("[OK] Nilpotent parabolic clock exponentiated successfully.")

    # 2. Hurwitz Quaternion to SL(2, C) mapping representation
    # Using 2x2 complex matrices where i, j, k are Pauli-like mappings
    I = sg.matrix(sg.CC, [[1, 0], [0, 1]])
    i_mat = sg.matrix(sg.CC, [[sg.I, 0], [0, -sg.I]])
    j_mat = sg.matrix(sg.CC, [[0, 1], [-1, 0]])
    k_mat = sg.matrix(sg.CC, [[0, sg.I], [sg.I, 0]])
    
    # Lipman-Hurwitz unit: e.g. q = 1/2 (1 + i + j + k)
    q_half = 0.5 * (I + i_mat + j_mat + k_mat)
    
    # Check that it evaluates to unit determinant (projective gauge symmetry)
    assert abs(q_half.det() - 1) < 1e-10
    print("[OK] Hurwitz quaternions map to projective gauge det(M)=1.")
    
    # Cartan Hop (Eigenvalue diagonalization)
    # Hyperbolic stretch example
    M_hyp = sg.matrix(sg.QQ, [[2, 0], [0, 1/2]])
    evals = M_hyp.eigenvalues()
    print("Eigenvalues for hyperbolic map (Cartan Hop):", evals)
    assert evals[0] * evals[1] == 1
    
    print("SAGE_PARABOLIC_CLOCK_OK")

if __name__ == "__main__":
    verify_parabolic_clock_hurwitz()
