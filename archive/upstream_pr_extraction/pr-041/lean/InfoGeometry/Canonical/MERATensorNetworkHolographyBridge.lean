import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real

namespace MERAHolography

/-- MERA Isometry Condition wᵗ w = 1. -/
abbrev MERAIsometry := {w : ℝ // w * w = 1}

namespace MERAIsometry

abbrev w_val (w : MERAIsometry) : ℝ := w.1
abbrev w_isometry (w : MERAIsometry) : w.w_val * w.w_val = 1 := w.2

variable (w : MERAIsometry)

/-- **Theorem**: MERA Isometry Norm Preservation: w² = 1. -/
theorem mera_isometry_norm_sq : w.w_val * w.w_val = 1 :=
  w.w_isometry

/-- MERA Holographic Geodesic Entanglement Cut Count S_MERA(L) = (c / 3) * ln(L). -/
def meraEntanglementCut (c L : ℝ) : ℝ :=
  (c / 3) * Real.log L

/-- **Theorem**: MERA Holographic Scale Step Increment S_MERA(2L) = S_MERA(L) + (c/3) * ln(2). -/
theorem mera_holographic_scale_step (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    meraEntanglementCut c (2 * L) = meraEntanglementCut c L + (c / 3) * Real.log 2 := by
  dsimp [meraEntanglementCut]
  have h_two_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have h_log_mul : Real.log (2 * L) = Real.log 2 + Real.log L := Real.log_mul h_two_ne hL_ne
  rw [h_log_mul]
  ring

end MERAIsometry

end MERAHolography
