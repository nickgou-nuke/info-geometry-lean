import sympy as sp

def verify_reversed_biquaternion_isomorphism():
    print("--- SymPy Biquaternion Isomorphism (Reversed Bivector Order) ---\n")
    I = sp.I
    Id = sp.eye(2)

    # 1. Clifford Generators (Pauli Matrices)
    sigma_1 = sp.Matrix([[0, 1],  [1, 0]])
    sigma_2 = sp.Matrix([[0, -I], [I, 0]])
    sigma_3 = sp.Matrix([[1, 0],  [0, -1]])
    generators = [sigma_1, sigma_2, sigma_3]

    # Verify Cl_{3,0}(R) anticommutation relations
    clifford_holds = True
    for i in range(3):
        for j in range(3):
            anticomm = sp.simplify(generators[i] * generators[j] + generators[j] * generators[i])
            expected = 2 * Id if i == j else sp.zeros(2)
            if anticomm != expected:
                clifford_holds = False
    print(f"[1] Clifford relations e_i e_j + e_j e_i = 2δ_ij I: {clifford_holds}")

    # 2. Hamilton Quaternions via Reversed Bivectors
    # Based on the design decision: i = σ₃σ₂, j = σ₁σ₃, k = σ₂σ₁
    quat_i = sigma_3 * sigma_2
    quat_j = sigma_1 * sigma_3
    quat_k = sigma_2 * sigma_1

    print("\n[2] Verifying Hamilton Relations for Even Subalgebra:")
    print(f"  -> i^2 = -Id: {sp.simplify(quat_i**2) == -Id}")
    print(f"  -> j^2 = -Id: {sp.simplify(quat_j**2) == -Id}")
    print(f"  -> k^2 = -Id: {sp.simplify(quat_k**2) == -Id}")
    print(f"  -> i*j = k:   {sp.simplify(quat_i * quat_j) == quat_k}")
    print(f"  -> i*j*k = -Id: {sp.simplify(quat_i * quat_j * quat_k) == -Id}")

    # 3. Pseudoscalar ω = e₁e₂e₃
    omega = sp.simplify(sigma_1 * sigma_2 * sigma_3)
    print("\n[3] Pseudoscalar Properties:")
    print(f"  -> ω^2 == -Id: {sp.simplify(omega**2) == -Id}")
    is_central = all(sp.simplify(omega * g - g * omega) == sp.zeros(2) for g in generators)
    print(f"  -> ω is central (commutes with all σ_i): {is_central}")
    print(f"  -> ω maps directly to i * Id: {omega == I * Id}")

if __name__ == "__main__":
    verify_reversed_biquaternion_isomorphism()
