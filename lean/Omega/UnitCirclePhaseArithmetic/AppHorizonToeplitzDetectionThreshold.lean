import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Rescaling the audited Toeplitz--PSD threshold by `C⁻¹` gives the paper's lower bound on the
required horizon length.
    thm:app-horizon-toeplitz-detection-threshold -/
theorem paper_app_horizon_toeplitz_detection_threshold
    (N C δ Qrho : ℝ) (C_pos : 0 < C)
    (hToeplitz : Qrho * Real.log (1 + δ * Qrho) ≤ C * N) :
    C⁻¹ * Qrho * Real.log (1 + δ * Qrho) ≤ N := by
  have hscaled :
      C⁻¹ * (Qrho * Real.log (1 + δ * Qrho)) ≤ C⁻¹ * (C * N) := by
    exact mul_le_mul_of_nonneg_left hToeplitz (inv_nonneg.mpr (le_of_lt C_pos))
  have hrewrite :
      C⁻¹ * (Qrho * Real.log (1 + δ * Qrho)) =
        C⁻¹ * Qrho * Real.log (1 + δ * Qrho) := by
    ring
  have hcancel : C⁻¹ * (C * N) = N := by
    calc
      C⁻¹ * (C * N) = (C⁻¹ * C) * N := by ring
      _ = N := by simp [ne_of_gt C_pos]
  rw [hrewrite, hcancel] at hscaled
  exact hscaled

end Omega.UnitCirclePhaseArithmetic
