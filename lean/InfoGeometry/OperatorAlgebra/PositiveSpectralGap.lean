/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Polynomial positivity and a gap above the zero spectral value

For a positive element `V` of an arbitrary unital complex C*-algebra, native
continuous functional calculus identifies `0 ≤ V ^ 2 - c • V` with exclusion
of the real spectral interval `(0, c)`. The zero spectral value is retained.
The algebra need not be commutative, finite dimensional, or represented by
diagonal operators, and `V` need not be invertible.

The parameter `c` may be any real number. A positive gap requires `0 < c`;
for the mass parameter in the intake one takes `c = m ^ 2` with `0 < m`.
Neither positivity nor nonvanishing constructs such a positive constant.
The final specialization uses the existing adjoint-paired Peirce Gram sum.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PositiveSpectralGap

/-- The scalar inequality used by the native functional calculus. -/
theorem scalar_quadratic_nonneg_iff {x c : ℝ} (hx : 0 ≤ x) :
    0 ≤ x ^ 2 - c * x ↔ x = 0 ∨ c ≤ x := by
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      apply (mul_le_mul_iff_right₀ hxpos).mp
      simpa only [pow_two, mul_comm] using (sub_nonneg.mp h)
  · rintro (rfl | hcx)
    · simp
    · apply sub_nonneg.mpr
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hcx hx

variable {B : Type*} [CStarAlgebra B]

/-- The functional calculus evaluates the actual operator polynomial. -/
theorem cfc_quadratic_defect (V : B) (c : ℝ) (hV : IsSelfAdjoint V) :
    cfc (fun x : ℝ => x ^ 2 - c * x) V = V ^ 2 - c • V := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun x : ℝ => c * x) V
      (continuousOn_id.pow 2) (continuousOn_const.mul continuousOn_id),
    cfc_pow_id (R := ℝ) V 2 hV, cfc_const_mul_id c V hV]

variable [PartialOrder B] [StarOrderedRing B]

/-- Polynomial positivity is equivalent to the precise gap above zero in
the native real spectrum of a positive element. -/
theorem nonneg_quadratic_defect_iff_spectrum (V : B) (c : ℝ) (hV : 0 ≤ V) :
    0 ≤ V ^ 2 - c • V ↔ ∀ x ∈ spectrum ℝ V, x = 0 ∨ c ≤ x := by
  have hsa : IsSelfAdjoint V := hV.isSelfAdjoint
  have hf : ContinuousOn (fun x : ℝ => x ^ 2 - c * x) (spectrum ℝ V) :=
    (continuousOn_id.pow 2).sub (continuousOn_const.mul continuousOn_id)
  rw [← cfc_quadratic_defect V c hsa,
    cfc_nonneg_iff (fun x : ℝ => x ^ 2 - c * x) V hf hsa]
  constructor
  · intro h x hx
    exact (scalar_quadratic_nonneg_iff (spectrum_nonneg_of_nonneg hV hx)).mp (h x hx)
  · intro h x hx
    exact (scalar_quadratic_nonneg_iff (spectrum_nonneg_of_nonneg hV hx)).mpr (h x hx)

/-- The same equivalence as an exact spectral support condition. -/
theorem spectrum_subset_zero_union_Ici_iff (V : B) (c : ℝ) (hV : 0 ≤ V) :
    spectrum ℝ V ⊆ ({0} : Set ℝ) ∪ Set.Ici c ↔ 0 ≤ V ^ 2 - c • V := by
  simpa only [Set.subset_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici] using
    (nonneg_quadratic_defect_iff_spectrum V c hV).symm

/-- One actual spectral value in the forbidden open interval refutes the
operator inequality; a zero eigenvalue alone does not refute it. -/
theorem not_nonneg_quadratic_defect_of_mem_spectrum
    (V : B) (c : ℝ) (hV : 0 ≤ V) {x : ℝ}
    (hx : x ∈ spectrum ℝ V) (hxpos : 0 < x) (hxc : x < c) :
    ¬ 0 ≤ V ^ 2 - c • V := by
  intro h
  rcases (nonneg_quadratic_defect_iff_spectrum V c hV).mp h x hx with hx0 | hcx
  · exact hxpos.ne' hx0
  · exact hxc.not_ge hcx

/-- Spectral values arbitrarily close to zero from above obstruct every
positive quadratic bound, even though the element itself is nonnegative. -/
theorem no_positive_quadratic_bound_of_spectrum_accumulates
    (V : B) (hV : 0 ≤ V)
    (hacc : ∀ c : ℝ, 0 < c →
      ∃ x : ℝ, x ∈ spectrum ℝ V ∧ 0 < x ∧ x < c) :
    ¬ ∃ c : ℝ, 0 < c ∧ 0 ≤ V ^ 2 - c • V := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨x, hx, hxpos, hxc⟩ := hacc c hc
  exact not_nonneg_quadratic_defect_of_mem_spectrum V c hV hx hxpos hxc hbound

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The criterion applies to the actual adjoint-paired Peirce interaction.
Self-adjointness of `P` supplies Gram positivity through the existing owner;
idempotence of `P` is not needed for this analytic implication. -/
theorem peirce_quadratic_defect_iff_spectrum
    {P : B} (hPs : star P = P) (X : B) (c : ℝ) :
    0 ≤ (genV P X (star X)) ^ 2 - c • genV P X (star X) ↔
      ∀ x ∈ spectrum ℝ (genV P X (star X)), x = 0 ∨ c ≤ x :=
  nonneg_quadratic_defect_iff_spectrum (genV P X (star X)) c
    (StarMetricNondegeneracy.genV_nonneg hPs X)

/-- At the squared mass threshold, the native spectral support condition
and the Peirce polynomial inequality are equivalent. For `m > 0` the
threshold is strictly positive; the theorem does not assert its existence. -/
theorem peirce_mass_gap_iff
    {P : B} (hPs : star P = P) (X : B) (m : ℝ) :
    spectrum ℝ (genV P X (star X)) ⊆ ({0} : Set ℝ) ∪ Set.Ici (m ^ 2) ↔
      0 ≤ (genV P X (star X)) ^ 2 - (m ^ 2) • genV P X (star X) :=
  spectrum_subset_zero_union_Ici_iff (genV P X (star X)) (m ^ 2)
    (StarMetricNondegeneracy.genV_nonneg hPs X)

end InfoGeometry.OperatorAlgebra.PositiveSpectralGap
