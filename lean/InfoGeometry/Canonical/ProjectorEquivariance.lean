import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.KK.QuasilatticeIndexInvariance
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ProjectorEquivariance

Coherence bridge for the two lawful projector/index presentations:

- fixed grading: negating the grading swaps `P₊` and `P₋` and flips the
  analytical index sign;
- transported grading: conjugacy along the transport flow preserves the
  analytical index exactly.

This file does not introduce a new projector ontology. It only packages the
two already-owned implementations in one place so downstream anomaly/gap files
can depend on the right one explicitly.
-/

namespace InfoGeometry.Canonical.ProjectorEquivariance

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.KK

section FixedGrading

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]
local notation "EndV" => V →ₗ[ℝ] V

/-- Negating the grading swaps the positive chiral projector with the negative one. -/
@[rep_depth transport, simp] theorem chiralProjectorPlus_neg_grading
    (Γ : EndV) :
    chiralProjectorPlus (-Γ) = chiralProjectorMinus Γ := by
  ext v
  simp [chiralProjectorPlus, chiralProjectorMinus, sub_eq_add_neg]

/-- Negating the grading swaps the negative chiral projector with the positive one. -/
@[rep_depth transport, simp] theorem chiralProjectorMinus_neg_grading
    (Γ : EndV) :
    chiralProjectorMinus (-Γ) = chiralProjectorPlus Γ := by
  ext v
  simp [chiralProjectorPlus, chiralProjectorMinus, sub_eq_add_neg]

/-- Fixed-grading sector swap packaged as a paired coherence theorem. -/
@[rep_depth transport] theorem fixed_grading_sector_swap
    (Γ : EndV) :
    chiralProjectorPlus (-Γ) = chiralProjectorMinus Γ ∧
      chiralProjectorMinus (-Γ) = chiralProjectorPlus Γ := by
  constructor <;> simp

variable [FiniteDimensional ℝ V]

/-- Under grading negation, the positive kernel slice becomes the negative one. -/
@[rep_depth transport, simp] theorem chiralKernelSlicePlus_neg_grading
    (D Γ : EndV) :
    chiralKernelSlicePlus D (-Γ) = chiralKernelSliceMinus D Γ := by
  simp [chiralKernelSlicePlus, chiralKernelSliceMinus]

/-- Under grading negation, the negative kernel slice becomes the positive one. -/
@[rep_depth transport, simp] theorem chiralKernelSliceMinus_neg_grading
    (D Γ : EndV) :
    chiralKernelSliceMinus D (-Γ) = chiralKernelSlicePlus D Γ := by
  simp [chiralKernelSlicePlus, chiralKernelSliceMinus]

/-- With fixed grading convention, negating the grading flips the analytical-index sign. -/
@[rep_depth transport] theorem analyticalIndex_neg_grading_eq_neg
    (D Γ : EndV) :
    analyticalIndex D (-Γ) = -analyticalIndex D Γ := by
  unfold analyticalIndex
  rw [chiralKernelSlicePlus_neg_grading, chiralKernelSliceMinus_neg_grading]
  abel

end FixedGrading

section TransportedGrading

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
local notation "EndV" => V →ₗ[ℝ] V

/--
Along a chiral conjugacy flow, the analytical index is constant when the
grading is transported with the Dirac lane.
-/
@[rep_depth transport] theorem analyticalIndex_eq_zero_time_of_conjugacy
    (D Γ : ℝ → EndV)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow)
    (s : ℝ) :
    analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0) := by
  exact (indexInvariantAlong_of_conjugacy D Γ eFlow hConj) s

/-- Alias name for the transported-grading analytical-index invariance lane. -/
@[rep_depth transport] theorem analyticalIndex_transport_invariance
    (D Γ : ℝ → EndV)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow)
    (s : ℝ) :
    analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0) := by
  exact analyticalIndex_eq_zero_time_of_conjugacy D Γ eFlow hConj s

end TransportedGrading

end InfoGeometry.Canonical.ProjectorEquivariance
