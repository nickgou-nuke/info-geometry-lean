import InfoGeometry.Lie.SouriauAffineCoadjointInfinitesimalBridge

/-!
# Souriau Affine Casimir Gradient Bridge

This file completes the generalized-Casimir vector equation in Souriau's thermodynamics.
It lifts the scalar calculus annihilation `dS_Q(V_xi(Q)) = 0` to a full vector equation
`V_{grad S(Q)}(Q) = 0` by introducing a dual pairing, gradient identification, and the 
fundamental skew-symmetry of the coadjoint and cocycle actions.
-/

namespace InfoGeometry.Lie.SouriauAffineCasimirGradientBridge

open InfoGeometry.Lie.SouriauAffineCoadjointInfinitesimalBridge
open InfoGeometry.Lie

noncomputable section

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]

/-- The Souriau pairing and gradient realization datum. -/
structure SouriauGradientDatum (M : Type*) (g : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup g] [NormedSpace ℝ g] where
  /-- The affine flow generator data. -/
  affineData : SouriauCoadjointDatum M g
  
  /-- The duality pairing between the Lie algebra and the moment space. -/
  pairing : g → M → ℝ
  /-- The pairing is bilinear. (Assuming bilinearity implicitly through typical usage, 
      but explicitly we just need the algebraic properties below). -/
  pairing_add_left : ∀ ξ₁ ξ₂ V, pairing (ξ₁ + ξ₂) V = pairing ξ₁ V + pairing ξ₂ V
  pairing_add_right : ∀ ξ V₁ V₂, pairing ξ (V₁ + V₂) = pairing ξ V₁ + pairing ξ V₂
  pairing_smul_left : ∀ (c : ℝ) ξ V, pairing (c • ξ) V = c * pairing ξ V
  
  /-- Nondegeneracy of the pairing in the second argument. -/
  nondegenerate : ∀ V : M, (∀ ξ : g, pairing ξ V = 0) → V = 0
  
  /-- The observable $S$ representing entropy/Casimir. -/
  S : M → ℝ
  /-- Its differential. -/
  dS : M → (M →L[ℝ] ℝ)
  /-- The gradient realization: $\nabla S(Q) \in \mathfrak{g}$. -/
  entropyGradient : M → g
  
  /-- Gradient identification: $\langle \nabla S(Q), V \rangle = dS_Q(V)$ for all $V$. -/
  entropyDifferential_eq_pairing : ∀ Q V,
    pairing (entropyGradient Q) V = dS Q V
    
  /-- Coadjoint action skew-symmetry: $\langle \xi, \operatorname{ad}^*_\beta Q \rangle = - \langle \beta, \operatorname{ad}^*_\xi Q \rangle$. -/
  coadjoint_pairing_skew : ∀ Q ξ β,
    pairing ξ (affineData.adStar β Q) = - pairing β (affineData.adStar ξ Q)
    
  /-- Cocycle skew-symmetry: $\langle \xi, \Theta(\beta) \rangle = - \langle \beta, \Theta(\xi) \rangle$. -/
  theta_pairing_skew : ∀ ξ β,
    pairing ξ (affineData.Theta β) = - pairing β (affineData.Theta ξ)

/-- The fundamental affine action skew-symmetry follows from its components. -/
theorem affineFundamental_pairing_skew (D : SouriauGradientDatum M g) (Q : M) (ξ β : g) :
    D.pairing ξ (D.affineData.adStar β Q + D.affineData.Theta β) =
    - D.pairing β (D.affineData.adStar ξ Q + D.affineData.Theta ξ) := by
  rw [D.pairing_add_right, D.pairing_add_right, D.coadjoint_pairing_skew, D.theta_pairing_skew, neg_add]

/-- The observable annihilates the affine fundamental vector field. -/
theorem affineCasimir_gradient_annihilates
    (D : SouriauGradientDatum M g)
    (A : AffineCoadjointInfinitesimalData M g)
    (h_match : A.datum = D.affineData)
    (h_inv : IsFlowInvariant A.toInfinitesimalCurveFamilyDatum D.S)
    (Q : M)
    (h_diff : HasFDerivAt D.S (D.dS Q) Q) :
    D.pairing (D.entropyGradient Q) (D.affineData.adStar A.generator Q + D.affineData.Theta A.generator) = 0 := by
  rw [D.entropyDifferential_eq_pairing]
  have h_anni := affineCasimir_annihilates_fundamentalVector A D.S (D.dS Q) h_inv Q h_diff
  rw [h_match] at h_anni
  exact h_anni

/-- The capstone generalized-Casimir vector equation. -/
theorem affineCasimir_generalizedCasimir_equation
    (D : SouriauGradientDatum M g)
    (h_anni : ∀ ξ Q, D.pairing (D.entropyGradient Q) (D.affineData.adStar ξ Q + D.affineData.Theta ξ) = 0)
    (Q : M) :
    D.affineData.adStar (D.entropyGradient Q) Q + D.affineData.Theta (D.entropyGradient Q) = 0 := by
  apply D.nondegenerate
  intro ξ
  rw [affineFundamental_pairing_skew D Q ξ (D.entropyGradient Q)]
  rw [h_anni ξ Q]
  exact neg_zero

end

end InfoGeometry.Lie.SouriauAffineCasimirGradientBridge
