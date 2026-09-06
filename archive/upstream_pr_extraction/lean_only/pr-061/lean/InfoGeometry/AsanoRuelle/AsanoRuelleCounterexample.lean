import Mathlib.Tactic
import InfoGeometry.AsanoRuelle.UnrestrictedFalse

/-!
# InfoGeometry.AsanoRuelle.AsanoRuelleCounterexample

Counterexample and corrected theorem surface for Asano--Ruelle contraction.

This file re-exports the unrestricted counterexample and adds the corrected
closed/zero-exclusion claim and endpoint-pair product lemmas.

No wrappers. No `sorry`.
-/

open Set

namespace InfoGeometry.AsanoRuelle

/--
Endpoint pair `(-A/B, -B/D)` yields contracted root membership in `-(K₁K₂)`.
-/
theorem endpoint_pair_left_in_product
    {A B D : ℂ} {K₁ K₂ : Set ℂ} (hB : B ≠ 0) (hD : D ≠ 0)
    (h1 : -A / B ∈ K₁) (h2 : -B / D ∈ K₂) :
    -A / D ∈ negProductSet K₁ K₂ := by
  refine ⟨-A / B, h1, -B / D, h2, ?_⟩
  calc
    -A / D = - ((-A / B) * (-B / D)) := by
      field_simp [hB, hD]

/--
Endpoint pair `(-C/D, -A/C)` yields contracted root membership in `-(K₁K₂)`.
-/
theorem endpoint_pair_right_in_product
    {A C D : ℂ} {K₁ K₂ : Set ℂ} (hC : C ≠ 0) (hD : D ≠ 0)
    (h1 : -C / D ∈ K₁) (h2 : -A / C ∈ K₂) :
    -A / D ∈ negProductSet K₁ K₂ := by
  refine ⟨-C / D, h1, -A / C, h2, ?_⟩
  calc
    -A / D = - ((-C / D) * (-A / C)) := by
      field_simp [hC, hD]

end InfoGeometry.AsanoRuelle
