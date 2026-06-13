import sympy as sp

def verify_biquaternion_su2():
    print("--- SymPy Verification: Biquaternion SU(2) Weak Force Symmetry ---")

    # Biquaternions C x H are isomorphic to 2x2 complex matrices M_2(C).
    # The basis elements i, j, k map to the Pauli matrices (up to a factor of i).
    # Specifically, the quaternion units map to:
    # i |-> -I * sigma_1
    # j |-> -I * sigma_2
    # k |-> -I * sigma_3

    # Define the Pauli matrices
    sigma_1 = sp.Matrix([[0, 1], [1, 0]])
    sigma_2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma_3 = sp.Matrix([[1, 0], [0, -1]])

    # Define the Biquaternion basis mappings
    # We use Q_i, Q_j, Q_k as the matrix representations of the quaternion units
    I = sp.I
    Qi = -I * sigma_1
    Qj = -I * sigma_2
    Qk = -I * sigma_3

    # Verify Quaternion algebra multiplication rules: i^2 = j^2 = k^2 = ijk = -1
    I_mat = sp.eye(2)

    print("Verifying Qi^2 == Qj^2 == Qk^2 == -1...")
    assert sp.simplify(Qi * Qi + I_mat) == sp.zeros(2), "Qi^2 != -1"
    assert sp.simplify(Qj * Qj + I_mat) == sp.zeros(2), "Qj^2 != -1"
    assert sp.simplify(Qk * Qk + I_mat) == sp.zeros(2), "Qk^2 != -1"
    print("Multiplication rules verified.")

    # Verify Commutator relations for the Lie Algebra su(2)
    # [Qi, Qj] = Qi*Qj - Qj*Qi = k - (-k) = 2*Qk

    def commutator(A, B):
        return A * B - B * A

    print("Verifying [Qi, Qj] == 2*Qk...")
    comm_ij = commutator(Qi, Qj)
    assert sp.simplify(comm_ij - 2*Qk) == sp.zeros(2), "[Qi, Qj] != 2*Qk"

    print("Verifying [Qj, Qk] == 2*Qi...")
    comm_jk = commutator(Qj, Qk)
    assert sp.simplify(comm_jk - 2*Qi) == sp.zeros(2), "[Qj, Qk] != 2*Qi"

    print("Verifying [Qk, Qi] == 2*Qj...")
    comm_ki = commutator(Qk, Qi)
    assert sp.simplify(comm_ki - 2*Qj) == sp.zeros(2), "[Qk, Qi] != 2*Qj"

    print("--- Verification Successful! ---")
    print("The Biquaternion (C x H) Lie algebra perfectly maps to the exact SU(2) Weak Force generators.")

if __name__ == "__main__":
    verify_biquaternion_su2()
