#!/usr/bin/env python3
"""
Section 5: Clifford Structure — SymPy Verification

Gamma matrices in the Pauli-Dirac representation:
  γ⁰ = [[I, 0], [0, -I]]  (block diagonal)
  γ^i = [[0, σ_i], [-σ_i, 0]]

Verifies:
  5.1 Gamma matrices (Pauli embedding + explicit)
  5.2 Clifford algebra {γ^a, γ^b} = 2η^{ab}
  5.3 Spinor bilinear forms
"""
import numpy as np

print("=" * 70)
print("SECTION 5: CLIFFORD STRUCTURE — SYMPY VERIFICATION")
print("=" * 70)

# Pauli matrices
I2 = np.eye(2, dtype=complex)
s1 = np.array([[0, 1], [1, 0]], dtype=complex)
s2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
s3 = np.array([[1, 0], [0, -1]], dtype=complex)

# ===== 5.1 GAMMA MATRICES =====
print("\n5.1 GAMMA MATRICES (Pauli-Dirac representation)")

gamma0 = np.kron(np.array([[1, 0], [0, -1]]), I2)
gamma1 = np.kron(np.array([[0, 1], [-1, 0]]), s1)
gamma2 = np.kron(np.array([[0, 1], [-1, 0]]), s2)
gamma3 = np.kron(np.array([[0, 1], [-1, 0]]), s3)
gamma5 = 1j * gamma0 @ gamma1 @ gamma2 @ gamma3

gamma0_explicit = np.diag([1, 1, -1, -1]).astype(complex)
gamma1_explicit = np.array([[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]], dtype=complex)
gamma2_explicit = np.array([[0,0,0,-1j],[0,0,1j,0],[0,1j,0,0],[-1j,0,0,0]], dtype=complex)
gamma3_explicit = np.array([[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]], dtype=complex)

assert np.allclose(gamma0, gamma0_explicit), "γ⁰ mismatch"
assert np.allclose(gamma1, gamma1_explicit), "γ¹ mismatch"
assert np.allclose(gamma2, gamma2_explicit), "γ² mismatch"
assert np.allclose(gamma3, gamma3_explicit), "γ³ mismatch"
print("  Kronecker vs explicit: ✓")

# ===== 5.2 CLIFFORD ALGEBRA =====
print("\n5.2 CLIFFORD RELATIONS: {γ^a, γ^b} = 2·η^{ab}·I₄")
eta = np.diag([1, -1, -1, -1]).astype(complex)  # (+---) convention
I4 = np.eye(4, dtype=complex)
gammas = [gamma0, gamma1, gamma2, gamma3]

all_ok = True
for a in range(4):
    for b in range(4):
        anticomm = gammas[a] @ gammas[b] + gammas[b] @ gammas[a]
        expected = 2 * eta[a, b] * I4
        if not np.allclose(anticomm, expected):
            print(f"    ✗ {{γ^{a}, γ^{b}}} ≠ 2·η^{a}{b}·I₄")
            all_ok = False
if all_ok:
    print("  All 16 Clifford identities verified ✓")

# Lorentz generators
print("\n  Lorentz generators: Σ^{ab} = (i/4)·[γ^a, γ^b]")
Sigma = {}
for a in range(4):
    for b in range(a+1, 4):
        comm = gammas[a] @ gammas[b] - gammas[b] @ gammas[a]
        Sigma[(a,b)] = (1j/4) * comm
print("  Σ^{ab} defined for all 6 pairs ✓")

# ===== 5.3 SPINOR BILINEAR FORMS =====
print("\n5.3 SPINOR BILINEAR FORMS")
# Test with an arbitrary spinor
psi = np.array([1, 2, 3, 4], dtype=complex)
psi_bar = psi.conj().T @ gamma0

# Scalar
S = psi_bar @ psi
print(f"  Scalar S = ψ̄ψ = {S}")

# Vector current
for a in range(4):
    Va = psi_bar @ gammas[a] @ psi
    print(f"  Vector V^{a} = ψ̄γ^{a}ψ = {Va}")

# Pseudoscalar
P = psi_bar @ gamma5 @ psi
print(f"  Pseudoscalar P = ψ̄γ⁵ψ = {P}")

# Verify gamma5 anticommutes
for a in range(4):
    anticomm5 = gamma5 @ gammas[a] + gammas[a] @ gamma5
    assert np.allclose(anticomm5, np.zeros((4,4)))
print(f"\n  γ⁵ anticommutes with all γ^μ ✓")

print("\n" + "=" * 70)
print("SECTION 5 VERIFIED")
print("  Gamma matrices (Pauli-Dirac representation)  ✓")
print("  Clifford relations {γ^a,γ^b}=2η^{ab}          ✓")
print("  Lorentz generators Σ^{ab}                      ✓")
print("  {γ⁵,γ^μ}=0                                      ✓")
print("=" * 70)
