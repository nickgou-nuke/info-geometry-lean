import Mathlib.Tactic
import InfoGeometry.Algebraic.CartanSouriauAffineCocycle

/-!
# Souriau Affine Casimir Entropy

This file defines the abstract algebraic condition for an entropy function
to be a Casimir invariant under the affine coadjoint action of a Lie group.
This avoids analytic/smoothness assumptions and captures the pure group-action
invariance of the entropy.

If the Massieu potential transforms with a Souriau cocycle, its Legendre-dual
entropy is an affine Casimir invariant.
-/

namespace InfoGeometry.Lie

open InfoGeometry.Algebraic.CartanSouriauAffineCocycle

variable {G M : Type*} [Group G] [AddCommGroup M]
variable (D : Datum (G := G) (M := M))

/-- An invariant function under the affine coadjoint action is called an affine Casimir. -/
def IsAffineCasimir (S : M → ℝ) : Prop :=
  ∀ g Q, S (affineAction D g Q) = S Q

theorem affineCasimir_one (S : M → ℝ) (h : IsAffineCasimir D S) (Q : M) :
    S (affineAction D 1 Q) = S Q := by
  rw [affineAction_one]

theorem affineCasimir_mul (S : M → ℝ) (h : IsAffineCasimir D S) (g h' : G) (Q : M) :
    S (affineAction D (g * h') Q) = S (affineAction D h' Q) := by
  rw [affineAction_mul, h g]

theorem affineCasimir_constant_on_affineOrbit (S : M → ℝ) (h : IsAffineCasimir D S) (g : G) (Q : M) :
    S (affineAction D g Q) = S Q :=
  h g Q

/-- If the Massieu potential transforms with the Souriau cocycle law:
  Φ(Ad_g β) = Φ(β) - ⟨θ(g⁻¹), β⟩
then the Legendre-dual Entropy S(Q) = ⟨Q, β_Q⟩ - Φ(β_Q)
is invariant under the affine coadjoint action.

Here we formulate the exact global algebraic signature as an open debt,
as the dual pairing ⟨Q, β⟩ requires a bilinear form and Ad/Ad* operators.
-/
theorem entropy_isAffineCasimir_of_massieu_transform
    {LieAlg : Type*} [AddCommGroup LieAlg]
    (pairing : M → LieAlg → ℝ)
    (Ad : G → LieAlg → LieAlg)
    (Massieu : LieAlg → ℝ)
    (Entropy : M → ℝ)
    -- Legendre duality: S(Q) = ⟨Q, β_Q⟩ - Φ(β_Q) for some β_Q
    (beta_of : M → LieAlg)
    (h_legendre : ∀ Q, Entropy Q = pairing Q (beta_of Q) - Massieu (beta_of Q))
    -- Massieu transforms with the cocycle
    (h_massieu : ∀ g β, Massieu (Ad g β) = Massieu β - pairing (D.theta g⁻¹) β)
    -- Coadjoint equivariance of pairing: ⟨affineAction g Q, Ad g β⟩ = ⟨Q, β⟩ + ⟨θ(g), Ad g β⟩
    (h_pairing : ∀ g Q β, pairing (affineAction D g Q) (Ad g β) = pairing Q β + pairing (D.theta g) (Ad g β))
    -- The inverse cocycle contribution is the negative transported cocycle.
    (h_theta_inverse_pairing : ∀ g β,
      pairing (D.theta g⁻¹) β = -pairing (D.theta g) (Ad g β))
    -- Adjoint action equivariance of the beta map: β_{affineAction g Q} = Ad g (β_Q)
    (h_beta : ∀ g Q, beta_of (affineAction D g Q) = Ad g (beta_of Q)) :
    IsAffineCasimir D Entropy := by
  intro g Q
  rw [h_legendre, h_beta, h_massieu, h_pairing]
  rw [h_theta_inverse_pairing]
  ring_nf
  exact (h_legendre Q).symm

end InfoGeometry.Lie
