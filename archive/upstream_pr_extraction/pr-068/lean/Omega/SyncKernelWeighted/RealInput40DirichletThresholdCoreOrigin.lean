import Mathlib

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The distinguished atom-factor root lies on the unit circle. -/
def atomRootsOnUnitCircle (atomRoot : ℂ) : Prop :=
  ‖atomRoot‖ = 1

/-- Any threshold mode with spectral radius larger than one must come from the core factor. -/
def thresholdModesComeFromCore (coreFactor : ℂ → ℂ) (thresholdRoot : ℂ) : Prop :=
  coreFactor thresholdRoot = 0

lemma atom_factor_root_norm_one {u z : ℂ} (hu : ‖u‖ = 1) (hz : 1 - u * z ^ 2 = 0) :
    ‖z‖ = 1 := by
  have hEq : u * z ^ 2 = 1 := (sub_eq_zero.mp hz).symm
  have hNorm : ‖u * z ^ 2‖ = (1 : ℝ) := by
    simpa using congrArg norm hEq
  have hSq : ‖z‖ ^ 2 = 1 := by
    simpa [hu, norm_mul, norm_pow] using hNorm
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

/-- Factor the Dirichlet threshold polynomial as `(1 - u z^2) F(z,u)`, use `|u| = 1` to place
every atom-factor root on the unit circle, and conclude that a threshold mode with spectral radius
greater than one must come from the core factor.
    thm:killo-real-input-40-dirichlet-threshold-core-origin -/
theorem paper_killo_real_input_40_dirichlet_threshold_core_origin
    (u : ℂ) (coreFactor : ℂ → ℂ) (atomRoot thresholdRoot : ℂ)
    (hu_unit : ‖u‖ = 1)
    (hatomRoot : 1 - u * atomRoot ^ 2 = 0)
    (hthresholdRadius : 1 < ‖thresholdRoot‖)
    (hthresholdFactorization :
      (1 - u * thresholdRoot ^ 2) * coreFactor thresholdRoot = 0) :
    atomRootsOnUnitCircle atomRoot ∧
      thresholdModesComeFromCore coreFactor thresholdRoot := by
  refine ⟨?_, ?_⟩
  · exact atom_factor_root_norm_one hu_unit hatomRoot
  · rcases mul_eq_zero.mp hthresholdFactorization with hAtom | hCore
    · have hUnit : ‖thresholdRoot‖ = 1 := atom_factor_root_norm_one hu_unit hAtom
      linarith [hthresholdRadius]
    · exact hCore

end

end Omega.SyncKernelWeighted
