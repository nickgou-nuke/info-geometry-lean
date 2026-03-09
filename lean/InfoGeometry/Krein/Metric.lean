import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.HilbertBridge
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neutral Metric Layer (Phase 2 Integration)

This module refactors the neutral Hessian metric properties to use the canonical
`KreinSpace` predicates on the `DoubledSpace` carrier.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InfoGeometry.Krein

/-! ### Coordinate-level Hessian (Off-diagonal) -/

/-- The neutral Hessian/Krein bilinear form on raw coordinates `(x, ξ)`. -/
noncomputable def hessianIndefiniteFormCoord
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) : ℝ :=
  ⟪v.1, w.2⟫_ℝ + ⟪w.1, v.2⟫_ℝ

/-- Bridge theorem: the coordinate Hessian form equals the diagonal Krein form
via the 45-degree rotation. -/
private lemma one_div_sqrt_two_sq_metric : ((1 / Real.sqrt 2 : ℝ) ^ 2) = (1 / 2 : ℝ) := by
  have hs0 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqrt : (Real.sqrt 2 : ℝ)^2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  field_simp [hs0]
  nlinarith [hsqrt]

lemma hessianIndefiniteFormCoord_eq_hessianDoubled (v w : E × E) :
    hessianIndefiniteFormCoord v w =
      hessianIndefiniteForm
        ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) v))
        ((NeutralSpace.rotation45 (E := E)).symm (NeutralSpace.toLp (E := E) w)) := by
  rcases v with ⟨x, ξ⟩
  rcases w with ⟨y, η⟩
  let c : ℝ := 1 / Real.sqrt 2
  have hc2 : c * c = (1 / 2 : ℝ) := by
    have hc2' : c ^ 2 = (1 / 2 : ℝ) := by simpa [c] using one_div_sqrt_two_sq_metric
    simpa [pow_two] using hc2'
  change
    ⟪x, η⟫_ℝ + ⟪y, ξ⟫_ℝ =
      hessianIndefiniteForm
        (InfoGeometry.Krein.toDoubled (c • x + c • ξ) (c • x - c • ξ))
        (InfoGeometry.Krein.toDoubled (c • y + c • η) (c • y - c • η))
  rw [InfoGeometry.Krein.hessianIndefiniteForm, kreinInner_prodL2]
  simp [InfoGeometry.Krein.toDoubled, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, sub_eq_add_neg]
  rw [real_inner_comm ξ y]
  ring_nf
  have hc2pow : c ^ 2 = (1 / 2 : ℝ) := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hc2
  rw [hc2pow]
  ring

end InfoGeometry.Krein

/-! ### Global Aliases -/

namespace InfoGeometry.Krein.NeutralSpace

/-- An operator on `NeutralSpace` is an infinitesimal isometry iff it is Krein-skew-adjoint. -/
def IsInfinitesimalIsometry (A : NeutralSpace E →L[ℝ] NeutralSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint A

/-- The Lie subalgebra of infinitesimal isometries for the neutral metric. -/
noncomputable def neutralLieSubalgebra :
    LieSubalgebra ℝ (NeutralSpace E →L[ℝ] NeutralSpace E) where
  carrier := {A | IsInfinitesimalIsometry A}
  zero_mem' := by
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg]
  add_mem' := by
    intro A B hA hB
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at hA hB ⊢
    simpa [hA, hB, add_comm, add_left_comm, add_assoc]
  smul_mem' := by
    intro c A hA
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at hA ⊢
    simpa [hA, smul_neg]
  lie_mem' := by
    intro A B hA hB
    simpa [IsInfinitesimalIsometry] using
      (KreinSpace.isKreinSkewAdjoint_lie (hA := hA) (hB := hB))

end InfoGeometry.Krein.NeutralSpace
