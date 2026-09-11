import InfoGeometry.Lie.SouriauAffineCasimirInfinitesimal
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Souriau Affine Coadjoint Infinitesimal Bridge

This file connects the generic infinitesimal curve family (calculus core) 
to the explicit affine coadjoint action formula required by Souriau's formulation 
of symplectic thermodynamics and moment maps.

The geometric generator of the affine flow is explicitly identified as:
`V_xi(Q) = ad*_xi Q + Theta(xi)`.
-/

namespace InfoGeometry.Lie.SouriauAffineCoadjointInfinitesimalBridge

open InfoGeometry.Lie

noncomputable section

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g]

/-- The Souriau coadjoint cycle data required to form the affine action. -/
structure SouriauCoadjointDatum (M : Type*) (g : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup g] [NormedSpace ℝ g] where
  /-- The coadjoint action vector field `ad*_xi Q`. -/
  adStar : g → M → M
  /-- The Souriau cocycle `Theta(xi)`. -/
  Theta : g → M

/-- 
The explicit geometric identification:
The infinitesimal velocity of the one-parameter family corresponds exactly
to the affine coadjoint action vector field.
-/
structure AffineCoadjointInfinitesimalData (M : Type*) (g : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup g] [NormedSpace ℝ g] extends InfinitesimalCurveFamilyDatum M where
  datum : SouriauCoadjointDatum M g
  generator : g
  /-- The crucial geometric identification $V_{\xi}(Q) = \operatorname{ad}^*_{\xi}Q + \Theta(\xi)$ -/
  infinitesimal_eq_affine_action : ∀ Q,
    infinitesimal Q = datum.adStar generator Q + datum.Theta generator

/--
The consequence of affine-orbit invariance:
The differential of any invariant scalar observable annihilates the
fundamental affine coadjoint vector field $ad^*_{\xi} Q + \Theta(\xi)$.

This is the infinitesimal affine-Casimir equation before asserting 
the global adjoint duality $dS_Q \leftrightarrow \partial S / \partial Q$.
-/
theorem affineCasimir_annihilates_fundamentalVector
    (A : AffineCoadjointInfinitesimalData M g)
    (S : M → ℝ) (dS_Q : M →L[ℝ] ℝ)
    (h_inv : IsFlowInvariant A.toInfinitesimalCurveFamilyDatum S)
    (Q : M)
    (h_diff : HasFDerivAt S dS_Q Q) :
    dS_Q (A.datum.adStar A.generator Q + A.datum.Theta A.generator) = 0 := by
  have h_anni := flow_invariant_annihilates_infinitesimal A.toInfinitesimalCurveFamilyDatum S dS_Q h_inv Q h_diff
  rw [A.infinitesimal_eq_affine_action Q] at h_anni
  exact h_anni

end

end InfoGeometry.Lie.SouriauAffineCoadjointInfinitesimalBridge
