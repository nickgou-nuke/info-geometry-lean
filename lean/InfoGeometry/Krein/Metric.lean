import InfoGeometry.Krein.HilbertBridge
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Ring

/-!
# Neutral Metric Layer (Phase 2 Integration)

This module refactors the neutral Hessian metric properties to use the canonical
`KreinSpace` predicates.

It establishes:
1. `preservesMetric` ↔ `IsKreinIsometry` on `NeutralSpace`.
2. `IsInfinitesimalIsometry` ↔ `IsKreinSkewAdjoint` on `NeutralSpace`.
3. The Lie algebra of infinitesimal isometries.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InfoGeometry.Krein

/-- The neutral Hessian/Krein bilinear form on doubled coordinates `(x, ξ)`.
This is the coordinate-level form used throughout projective and prequantum layers. -/
noncomputable def hessianIndefiniteForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) : ℝ :=
  ⟪v.1, w.2⟫_ℝ + ⟪w.1, v.2⟫_ℝ

lemma hessianIndefiniteForm_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) :
    hessianIndefiniteForm (E := E) v w = ⟪v.1, w.2⟫_ℝ + ⟪w.1, v.2⟫_ℝ := rfl

@[simp] lemma hessianIndefiniteForm_zero_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    hessianIndefiniteForm (E := E) (0 : E × E) 0 = 0 := by
  simp [hessianIndefiniteForm]

/-- Bridge theorem: the coordinate Hessian form equals the canonical neutral Krein form
via `NeutralSpace.toLp`. -/
lemma hessianIndefiniteForm_eq_kreinInner (v w : E × E) :
    hessianIndefiniteForm (E := E) v w =
      KreinSpace.kreinInner (NeutralSpace.toLp (E := E) v) (NeutralSpace.toLp (E := E) w) := by
  calc
    hessianIndefiniteForm (E := E) v w
        = ⟪v.1, w.2⟫_ℝ + ⟪v.2, w.1⟫_ℝ := by
            simp [hessianIndefiniteForm, real_inner_comm]
    _ = KreinSpace.kreinInner (NeutralSpace.toLp (E := E) v) (NeutralSpace.toLp (E := E) w) := by
            simpa [NeutralSpace.ofLp_toLp] using
              (NeutralSpace.kreinInner_eq_hessian (E := E)
                (NeutralSpace.toLp (E := E) v) (NeutralSpace.toLp (E := E) w)).symm

end InfoGeometry.Krein

namespace InfoGeometry

/-- Backward-compatible global alias for the neutral Hessian form on doubled coordinates. -/
noncomputable abbrev hessianIndefiniteForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) : ℝ :=
  Krein.hessianIndefiniteForm (E := E) v w

lemma hessianIndefiniteForm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) :
    hessianIndefiniteForm (E := E) v w = Krein.hessianIndefiniteForm (E := E) v w := rfl

lemma hessianIndefiniteForm_eq_kreinInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (v w : E × E) :
    hessianIndefiniteForm (E := E) v w =
      KreinSpace.kreinInner (Krein.NeutralSpace.toLp (E := E) v)
        (Krein.NeutralSpace.toLp (E := E) w) :=
  Krein.hessianIndefiniteForm_eq_kreinInner (E := E) v w

end InfoGeometry

/-- Global compatibility alias for the neutral Hessian form on doubled coordinates. -/
noncomputable abbrev hessianIndefiniteForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) : ℝ :=
  InfoGeometry.Krein.hessianIndefiniteForm (E := E) v w

lemma hessianIndefiniteForm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E × E) :
    hessianIndefiniteForm (E := E) v w = InfoGeometry.Krein.hessianIndefiniteForm (E := E) v w := rfl

namespace InfoGeometry.Krein.NeutralSpace

/-- An operator on `NeutralSpace` preserves the Hessian metric iff it is a Krein isometry. -/
abbrev preservesMetric (U : NeutralSpace E →L[ℝ] NeutralSpace E) : Prop :=
  KreinSpace.IsKreinIsometry U

/-- An operator on `NeutralSpace` is an infinitesimal isometry iff it is Krein-skew-adjoint. -/
def IsInfinitesimalIsometry (A : NeutralSpace E →L[ℝ] NeutralSpace E) : Prop :=
  KreinSpace.IsKreinSkewAdjoint A

/-- Project out the first component of a NeutralSpace vector. -/
noncomputable def fst (u : NeutralSpace E) : E := (WithLp.equiv 2 (E × E) u.val).1

/-- Project out the second component of a NeutralSpace vector. -/
noncomputable def snd (u : NeutralSpace E) : E := (WithLp.equiv 2 (E × E) u.val).2

lemma infinitesimalIsometry_iff_hessian (A : NeutralSpace E →L[ℝ] NeutralSpace E) :
    IsInfinitesimalIsometry A ↔
    ∀ v w : NeutralSpace E,
      ⟪fst (A v), snd w⟫_ℝ + ⟪snd (A v), fst w⟫_ℝ +
      ⟪fst v, snd (A w)⟫_ℝ + ⟪snd v, fst (A w)⟫_ℝ = 0 := by
  rw [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff]
  simp only [kreinInner_eq_hessian, add_assoc]
  unfold fst snd
  rfl

/-- The Lie subalgebra of infinitesimal isometries for the neutral metric. -/
noncomputable def neutralLieSubalgebra :
    LieSubalgebra ℝ (NeutralSpace E →L[ℝ] NeutralSpace E) where
  carrier := {A | IsInfinitesimalIsometry A}
  zero_mem' := by
    rw [Set.mem_setOf_eq, IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg]
    simp
  add_mem' := by
    intro A B hA hB; rw [Set.mem_setOf_eq] at *
    simp only [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_add, hA, hB, neg_add]
  smul_mem' := by
    intro c A hA; rw [Set.mem_setOf_eq] at *
    simp only [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_smul, hA, smul_neg]
  lie_mem' := by
    intro A B hA hB; rw [Set.mem_setOf_eq] at *
    simp only [IsInfinitesimalIsometry, KreinSpace.isKreinSkewAdjoint_iff_eq_neg] at *
    rw [KreinSpace.kreinAdjoint_lie, hA, hB]
    simp [lie_skew]

end InfoGeometry.Krein.NeutralSpace
