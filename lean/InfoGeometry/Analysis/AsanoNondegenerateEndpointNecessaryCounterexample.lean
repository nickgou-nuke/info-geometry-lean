/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.AsanoContractionNative

/-!
# Counterexample: nondegenerate Asano localization needs an endpoint hypothesis

Zero-freeness of the two-variable block alone does not localize every zero of
the contracted affine polynomial to the signed product of the forbidden sets.
The missing endpoint alternative in `AsanoContractionNative` is essential.
-/

namespace InfoGeometry.Analysis.AsanoContractionNative

private def counterexampleK₁ : Set ℂ := {z | z ≠ 0}
private def counterexampleK₂ : Set ℂ := ∅

/-- A zero-free two-variable polynomial with nonzero determinant whose
contracted polynomial has a root outside the signed-product set. -/
theorem nondegenerate_zero_free_does_not_localize_contracted_root :
    ∃ K₁ K₂ : Set ℂ, ∃ A B C D z : ℂ,
      (0 : ℂ) ∉ K₁ ∧ (0 : ℂ) ∉ K₂ ∧
      ZeroFreeOutside K₁ K₂ A B C D ∧
      D ≠ 0 ∧ A * D - B * C ≠ 0 ∧
      IsContractedZero A D z ∧ z ∉ signedProductSet K₁ K₂ := by
  refine ⟨counterexampleK₁, counterexampleK₂, 1, 0, 0, 1, -1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [counterexampleK₁]
  · simp [counterexampleK₂]
  · intro z₁ z₂ hz₁ hz₂
    have hz₁_zero : z₁ = 0 := by
      simpa [counterexampleK₁] using hz₁
    simp [ZeroFreeOutside, asanoPoly, hz₁_zero]
  · norm_num
  · norm_num
  · norm_num [IsContractedZero, asanoContract]
  · simp [signedProductSet, counterexampleK₂]

/-- The endpoint alternative genuinely fails in the counterexample: both
cross-coefficients vanish. -/
theorem endpoint_alternative_fails_in_counterexample :
    ¬ ((0 : ℂ) ≠ 0 ∧ -(0 / (1 : ℂ)) ∈ counterexampleK₁ ∨
        (0 : ℂ) ≠ 0 ∧ -(0 / (1 : ℂ)) ∈ counterexampleK₂) := by
  simp [counterexampleK₁, counterexampleK₂]

end InfoGeometry.Analysis.AsanoContractionNative
