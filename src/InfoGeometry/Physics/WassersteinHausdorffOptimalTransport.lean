import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Kantorovich pairing and native Hausdorff scaling

The pairing below is the fixed-observable term in the Kantorovich--Rubinstein
dual formula.  It is not itself a Wasserstein distance: no supremum over a
Lipschitz class is introduced here.  Hausdorff scaling is taken directly from
Mathlib's metric-measure theorem, rather than stored as a structure field.
-/

namespace InfoGeometry.Physics

open scoped Pointwise

variable {BoundaryState : Type*}

def kantorovichPairing
    (Expectation : BoundaryState → (BoundaryState → ℝ) → ℝ)
    (ρ σ : BoundaryState) (f : BoundaryState → ℝ) : ℝ :=
  |Expectation ρ f - Expectation σ f|

theorem kantorovichPairing_symm
    (Expectation : BoundaryState → (BoundaryState → ℝ) → ℝ)
    (ρ σ : BoundaryState) (f : BoundaryState → ℝ) :
  kantorovichPairing Expectation ρ σ f =
      kantorovichPairing Expectation σ ρ f := by
  exact abs_sub_comm (Expectation ρ f) (Expectation σ f)

theorem kantorovichPairing_triangle
    (Expectation : BoundaryState → (BoundaryState → ℝ) → ℝ)
    (ρ σ τ : BoundaryState) (f : BoundaryState → ℝ) :
    kantorovichPairing Expectation ρ τ f ≤
      kantorovichPairing Expectation ρ σ f +
        kantorovichPairing Expectation σ τ f := by
  dsimp [kantorovichPairing]
  rw [show Expectation ρ f - Expectation τ f =
      (Expectation ρ f - Expectation σ f) +
        (Expectation σ f - Expectation τ f) by ring]
  exact abs_add_le _ _

theorem hausdorffMeasure_real_smul
    {d : ℝ} (hd : 0 ≤ d) {c : ℝ} (hc : c ≠ 0) (s : Set ℝ) :
    MeasureTheory.Measure.hausdorffMeasure d (c • s) =
      ‖c‖₊ ^ d • MeasureTheory.Measure.hausdorffMeasure d s := by
  exact MeasureTheory.Measure.hausdorffMeasure_smul₀ hd hc s

theorem hausdorffMeasure_real_double_smul
    {d : ℝ} (hd : 0 ≤ d) {c₁ c₂ : ℝ}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (s : Set ℝ) :
    MeasureTheory.Measure.hausdorffMeasure d (c₁ • (c₂ • s)) =
      ‖c₁‖₊ ^ d • (‖c₂‖₊ ^ d •
        MeasureTheory.Measure.hausdorffMeasure d s) := by
  rw [hausdorffMeasure_real_smul hd hc₁, hausdorffMeasure_real_smul hd hc₂]

end InfoGeometry.Physics
