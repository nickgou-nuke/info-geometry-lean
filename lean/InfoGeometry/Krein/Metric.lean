import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.HilbertBridge
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
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

/-! ### DoubledSpace Hessian (Diagonal) -/

/-- The Hessian indefinite form on the canonical `DoubledSpace` carrier.
This is exactly the Krein inner product in the diagonal basis. -/
noncomputable def hessianIndefiniteForm (u v : DoubledSpace E) : ℝ :=
  KreinSpace.kreinInner u v

/-- Bridge theorem: the coordinate Hessian form equals the diagonal Krein form
via the 45-degree rotation. -/
lemma hessianIndefiniteFormCoord_eq_hessianDoubled (v w : E × E) :
    hessianIndefiniteFormCoord v w =
      hessianIndefiniteForm ((rotation45 E).invFun (NeutralSpace.toLp v))
                            ((rotation45 E).invFun (NeutralSpace.toLp w)) := by
  sorry

end InfoGeometry.Krein

/-! ### Global Aliases -/

noncomputable abbrev hessianIndefiniteForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : InfoGeometry.Krein.DoubledSpace E) : ℝ :=
  InfoGeometry.Krein.hessianIndefiniteForm u v

namespace InfoGeometry.Krein.NeutralSpace

/-- An operator on `NeutralSpace` is an infinitesimal isometry iff it is Krein-skew-adjoint. -/
def IsInfinitesimalIsometry (A : NeutralSpace E →L[ℝ] NeutralSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint A

/-- The Lie subalgebra of infinitesimal isometries for the neutral metric. -/
noncomputable def neutralLieSubalgebra :
    LieSubalgebra ℝ (NeutralSpace E →L[ℝ] NeutralSpace E) where
  carrier := {A | IsInfinitesimalIsometry A}
  zero_mem' := by simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg]
  add_mem' hA hB := by
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_add, hA, hB, neg_add]
  smul_mem' c A hA := by
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_smul, hA, smul_neg]
  lie_mem' hA hB := by
    simp [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_lie, hA, hB]
    simp [Ring.lie_def, neg_mul, mul_neg, neg_neg]
    rw [neg_sub, add_comm]

end InfoGeometry.Krein.NeutralSpace
