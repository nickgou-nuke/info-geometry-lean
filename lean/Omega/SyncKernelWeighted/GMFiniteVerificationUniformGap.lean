import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Uniform twisted gap on the full nonresonant window above the bootstrap scale. -/
def uniform_gap_holds
    (window : Set ℝ) (baseScale : ℕ) (gap : ℝ → ℕ → ℝ) (targetGap : ℝ) : Prop :=
  ∀ {θ : ℝ}, θ ∈ window → ∀ {N : ℕ}, baseScale ≤ N → gap θ N ≤ targetGap

/-- Finite verification on the sampled frequencies and sampled scales. -/
def finite_checks_pass
    (frequencySet : Finset ℝ) (scaleSet : Finset ℕ) (gap : ℝ → ℕ → ℝ)
    (targetGap : ℝ) : Prop :=
  ∀ {θ : ℝ}, θ ∈ frequencySet → ∀ {M : ℕ}, M ∈ scaleSet → gap θ M ≤ targetGap

/-- Paper label: `thm:gm-finite-verification-uniform-gap`. Restricting the uniform gap to the
finite sample set gives the forward implication, and the reverse implication combines the finite
frequency cover of the nonresonant window with the scale-bootstrap principle. -/
theorem paper_gm_finite_verification_uniform_gap
    (frequencySet : Finset ℝ) (scaleSet : Finset ℕ) (window : Set ℝ)
    (baseScale : ℕ) (gap : ℝ → ℕ → ℝ) (targetGap : ℝ)
    (sampled_frequency_mem_window :
      ∀ {θ : ℝ}, θ ∈ frequencySet → θ ∈ window)
    (sampled_scale_large :
      ∀ {M : ℕ}, M ∈ scaleSet → baseScale ≤ M)
    (frequency_window_cover :
      ∀ {θ : ℝ}, θ ∈ window →
        ∃ θ0 ∈ frequencySet, ∀ {M : ℕ}, baseScale ≤ M → gap θ M ≤ gap θ0 M)
    (scale_bootstrap :
      ∀ {θ : ℝ}, θ ∈ frequencySet →
        (∀ {M : ℕ}, M ∈ scaleSet → gap θ M ≤ targetGap) →
          ∀ {N : ℕ}, baseScale ≤ N → gap θ N ≤ targetGap) :
    uniform_gap_holds window baseScale gap targetGap ↔
      finite_checks_pass frequencySet scaleSet gap targetGap := by
  constructor
  · intro hUniform θ hθ M hM
    exact hUniform (sampled_frequency_mem_window hθ) (sampled_scale_large hM)
  · intro hFinite θ hθ N hN
    rcases frequency_window_cover hθ with ⟨θ0, hθ0, hcompare⟩
    exact le_trans (hcompare hN) <| scale_bootstrap hθ0 (fun hM => hFinite hθ0 hM) hN

end Omega.SyncKernelWeighted
