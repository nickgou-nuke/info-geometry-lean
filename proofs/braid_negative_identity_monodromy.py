"""SymPy witness: braid full twists as negative-identity spinor monodromy.

This is the bridge from the Pauli/biquaternion root equation X^k=-I to braid
monodromy.  We use the local spinor half-twist gate

    g = i σ₂ = [[0, 1], [-1, 0]],      g² = -I.

For B₂, the central full twist is σ₁², so its image is -I.  For B₃, the
Garside half twist is Δ=σ₁σ₂σ₁ and the central full twist is Δ²=(σ₁σ₂)³.
In the uniform spinor phase channel σᵢ↦g, Artin relations hold and Δ² maps to
`g^6=-I`.  This realizes the spinorial rule: a full 2π braid rotation acts by
negative identity.
"""

import sympy as sp


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


I2 = sp.eye(2)
g = sp.Matrix([[0, 1], [-1, 0]])  # i σ₂ real form

print("§1  Local spinor half-twist gate")
assert_matrix_zero("g^2 = -I", g**2 + I2)
assert_matrix_zero("g^4 = I", g**4 - I2)
print("   g=iσ₂ has g²=-I and g⁴=I ✓")

print("§2  B₂ central full twist")
sigma1 = g
Delta_B2 = sigma1
full_B2 = Delta_B2**2
assert_matrix_zero("ρ(Δ²_B2)=-I", full_B2 + I2)
print("   B₂: ρ(σ₁²)=ρ(Δ²)=-I ✓")

print("§3  B₃ Artin relation and central full twist")
sigma1 = g
sigma2 = g
assert_matrix_zero("σ1 σ2 σ1 = σ2 σ1 σ2", sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2)
Delta_B3 = sigma1 * sigma2 * sigma1
full_B3_via_Delta = Delta_B3**2
full_B3_via_center_word = (sigma1 * sigma2)**3
assert_matrix_zero("Δ²=(σ1σ2)^3 under representation", full_B3_via_Delta - full_B3_via_center_word)
assert_matrix_zero("ρ(Δ²_B3)=-I", full_B3_via_Delta + I2)
print("   B₃: Artin relation holds and ρ(Δ²)=-I ✓")

print("§4  Logarithmic monodromy connection")
# Since g has eigenvalues ±i, one branch of log(g) has eigenvalues ±πi/2.
L = sp.diag(sp.I * sp.pi / 2, -sp.I * sp.pi / 2)
Delta_diag = sp.diag(sp.I, -sp.I)
assert_matrix_zero("exp(L)=diag(i,-i)", L.exp() - Delta_diag)
assert_matrix_zero("exp(2L)=-I", (2 * L).exp() + I2)
print("   logarithm branch has half-integer spectrum and doubles to -I ✓")

print()
print("braid_negative_identity_monodromy.py: All identities verified")
