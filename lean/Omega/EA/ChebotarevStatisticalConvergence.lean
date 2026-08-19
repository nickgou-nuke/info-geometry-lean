import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.EA.ChebotarevSecondMainTerm

namespace Omega.EA

/-- Paper-facing wrapper assembling the TV, chi-square, KL, square-root-gap, and witness
obstruction claims for the primitive Chebotarev statistical-convergence regime.
    thm:kernel-chebotarev-statistical-convergence -/
theorem paper_kernel_chebotarev_statistical_convergence
    (tvDistance chiSqDistance klDistance sqrtGapDistance : ℕ → ℝ)
    (tau lambda tvConstant chiSqConstant klConstant sqrtGapConstant witnessCoeff : ℝ)
    (tvBound_h : ∀ n : ℕ, |tvDistance n| ≤ tvConstant * tau ^ n)
    (chiSqBound_h : ∀ n : ℕ, |chiSqDistance n| ≤ chiSqConstant * tau ^ (2 * n))
    (klBound_h : ∀ n : ℕ, |klDistance n| ≤ klConstant * tau ^ (2 * n))
    (sqrtGapRate_h : ∀ n : ℕ, |sqrtGapDistance n| ≤ sqrtGapConstant * lambda ^ n)
    (witnessCoeff_ne_zero : witnessCoeff ≠ 0) :
    (∀ n : ℕ, |tvDistance n| ≤ tvConstant * tau ^ n) ∧
      (∀ n : ℕ, |chiSqDistance n| ≤ chiSqConstant * tau ^ (2 * n)) ∧
      (∀ n : ℕ, |klDistance n| ≤ klConstant * tau ^ (2 * n)) ∧
      (∀ n : ℕ, |sqrtGapDistance n| ≤ sqrtGapConstant * lambda ^ n) ∧
      spectralProjection witnessCoeff ≠ 0 ∧
      chebotarevOscillationLowerBound witnessCoeff := by
  refine ⟨tvBound_h, chiSqBound_h, klBound_h, sqrtGapRate_h, ?_⟩
  · rcases
      kernel_chebotarev_second_main_term witnessCoeff witnessCoeff_ne_zero with
        ⟨_hexp, hnonzero, hosc⟩
    exact ⟨hnonzero, hosc⟩

end Omega.EA
