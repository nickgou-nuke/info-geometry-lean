import Mathlib.MeasureTheory.Measure.MeasureSpace
/-!
# Unnormalized States and Projective Rays

This module defines the foundational state space for information geometry:
unnormalized positive measures. Normalization is treated as a gauge choice,
and the true geometric primitive is the projective ray of measures.
-/

namespace InfoGeometry.Measure

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- An unnormalized state is just a measure. We typically restrict to finite measures. -/
abbrev State (α : Type*) [MeasurableSpace α] := Measure α

/-- Two measures live on the same projective ray if they are related by a strict positive scalar. -/
def SameRay (mu nu : State α) : Prop :=
  ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ mu = c • nu

/-- `SameRay` is an equivalence relation on measures. -/
lemma SameRay_refl (mu : State α) : SameRay mu mu :=
  ⟨1, by norm_num, by norm_num, (one_smul _ _).symm⟩

lemma SameRay_symm {mu nu : State α} (h : SameRay mu nu) : SameRay nu mu := by
  rcases h with ⟨c, hc_ne_zero, hc_ne_top, hmu⟩
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hc_ne_top, ENNReal.inv_ne_top.mpr hc_ne_zero, ?_⟩
  rw [hmu, smul_smul, ENNReal.inv_mul_cancel hc_ne_zero hc_ne_top, one_smul]

lemma SameRay_trans {mu nu rho : State α} (h1 : SameRay mu nu) (h2 : SameRay nu rho) :
    SameRay mu rho := by
  rcases h1 with ⟨c1, hc1_ne_zero, hc1_ne_top, hmu⟩
  rcases h2 with ⟨c2, hc2_ne_zero, hc2_ne_top, hnu⟩
  refine ⟨c1 * c2, mul_ne_zero hc1_ne_zero hc2_ne_zero, ENNReal.mul_ne_top hc1_ne_top hc2_ne_top, ?_⟩
  rw [hmu, hnu, smul_smul]

end InfoGeometry.Measure
