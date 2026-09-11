import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
Re-export of the unrestricted counterexample theorem.
-/
theorem unrestricted_asano_contraction_statement_false_reexport :
    ¬ (∀ (A B C D : ℂ) (K₁ K₂ : Set ℂ),
        (∀ z₁ : ℂ, z₁ ∉ K₁ →
          ∀ z₂ : ℂ, z₂ ∉ K₂ →
            A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0) →
        ∀ z : ℂ,
          z ∉ negProductSet K₁ K₂ →
            A + D * z ≠ 0) :=
  unrestricted_asano_contraction_statement_false

/--
Corrected Asano-Ruelle contraction statement (closed sets + origin exclusion).
-/
def CorrectedAsanoRuelleClaim : Prop :=
  ∀ (A B C D : ℂ) (K₁ K₂ : Set ℂ),
    IsClosed K₁ →
    IsClosed K₂ →
    (0 : ℂ) ∉ K₁ →
    (0 : ℂ) ∉ K₂ →
    (∀ z₁ : ℂ, z₁ ∉ K₁ →
      ∀ z₂ : ℂ, z₂ ∉ K₂ →
        A + B * z₁ + C * z₂ + D * z₁ * z₂ ≠ 0) →
    ∀ z : ℂ, z ∉ negProductSet K₁ K₂ →
      A + D * z ≠ 0

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
