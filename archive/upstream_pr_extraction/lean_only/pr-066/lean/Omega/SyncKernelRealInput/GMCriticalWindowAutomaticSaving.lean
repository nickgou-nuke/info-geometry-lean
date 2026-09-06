import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Paper label: `cor:gm-critical-window-automatic-saving`. The automatic moment-saving
hypothesis supplies a positive exponent witness, and the critical scalings expose the
large-value bound at `T = N^(6/5)` and `V` proportional to `N^(3/4)`. -/
theorem paper_gm_critical_window_automatic_saving
    (N T V thresholdConstant largeValueCount savingEpsilon : ℝ)
    (savingEpsilon_pos : 0 < savingEpsilon)
    (criticalScaling : T = N ^ (6 / 5 : ℝ))
    (thresholdScaling : V = thresholdConstant * N ^ (3 / 4 : ℝ))
    (automaticMomentSaving :
      largeValueCount ≤ N ^ (12 / 5 - savingEpsilon : ℝ) * V ^ (-(4 : ℝ))) :
    ∃ ε : ℝ,
      0 < ε ∧
        T = N ^ (6 / 5 : ℝ) ∧
        V = thresholdConstant * N ^ (3 / 4 : ℝ) ∧
        largeValueCount ≤ N ^ (12 / 5 - ε : ℝ) * V ^ (-(4 : ℝ)) := by
  exact ⟨savingEpsilon, savingEpsilon_pos, criticalScaling, thresholdScaling,
    automaticMomentSaving⟩

end

/-- The displayed exponent before the `V^{-4}` factor. -/
def gm_critical_window_automatic_saving_displayExponent
    (TExp eps : ℚ) : ℚ :=
  TExp + 6 / 5 - eps

/-- The total exponent after substituting the critical threshold `V = N^(3/4)`. -/
def gm_critical_window_automatic_saving_totalExponent
    (TExp VExp eps : ℚ) : ℚ :=
  gm_critical_window_automatic_saving_displayExponent TExp eps - 4 * VExp

/-- The critical-window rational exponent calculation. -/
def gm_critical_window_automatic_saving_statement
    (TExp VExp eps : ℚ) : Prop :=
  gm_critical_window_automatic_saving_displayExponent TExp eps = 12 / 5 - eps ∧
    gm_critical_window_automatic_saving_totalExponent TExp VExp eps = -3 / 5 - eps ∧
      0 < eps

/-- The algebra behind the displayed large-values exponent after substituting
`T = N^(6/5)` and `V = N^(3/4)`. -/
theorem gm_critical_window_automatic_saving_exponent_algebra
    (TExp VExp eps : ℚ)
    (TExp_eq : TExp = 6 / 5)
    (VExp_eq : VExp = 3 / 4)
    (eps_pos : 0 < eps) :
    gm_critical_window_automatic_saving_statement TExp VExp eps := by
  refine ⟨?_, ?_, eps_pos⟩
  · unfold gm_critical_window_automatic_saving_displayExponent
    rw [TExp_eq]
    ring
  · unfold gm_critical_window_automatic_saving_totalExponent
      gm_critical_window_automatic_saving_displayExponent
    rw [TExp_eq, VExp_eq]
    ring

end Omega.SyncKernelRealInput
