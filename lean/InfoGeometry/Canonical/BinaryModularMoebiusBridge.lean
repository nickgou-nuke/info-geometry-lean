import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.ModularTheory

open Real

/-!
# Binary Relative Modular Operator and Möbius Bridge
-/

/-- The standard logit function. -/
noncomputable def logit (x : ℝ) : ℝ := log (x / (1 - x))

/-- 
A strict binary state space prior `pi = (alpha, 1 - alpha)`. 
-/
structure StrictBinaryState where
  prob : ℝ
  h_pos : 0 < prob
  h_lt_one : prob < 1

namespace StrictBinaryState

variable (pi p : StrictBinaryState)

/-- The relative modular operator Δ_{p|pi} -/
noncomputable def relativeModularOp : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![p.prob / pi.prob, (1 - p.prob) / (1 - pi.prob)]

/-- The positive modular eigenvalue Δ_+ = r / alpha. -/
noncomputable def deltaPlus : ℝ := p.prob / pi.prob

/-- The negative modular eigenvalue Δ_- = (1 - r) / (1 - alpha). -/
noncomputable def deltaMinus : ℝ := (1 - p.prob) / (1 - pi.prob)

theorem deltaPlus_pos : 0 < deltaPlus pi p := 
  div_pos p.h_pos pi.h_pos

theorem deltaMinus_pos : 0 < deltaMinus pi p := 
  div_pos (sub_pos_of_lt p.h_lt_one) (sub_pos_of_lt pi.h_lt_one)

theorem log_spectral_gap_eq_logit_diff :
    log (deltaPlus pi p / deltaMinus pi p) = logit p.prob - logit pi.prob := by
  dsimp [deltaPlus, deltaMinus, logit]
  have h_div_rearrange : (p.prob / pi.prob) / ((1 - p.prob) / (1 - pi.prob)) = 
      (p.prob / (1 - p.prob)) / (pi.prob / (1 - pi.prob)) := by
    rw [div_div_div_comm]
  rw [h_div_rearrange]
  have hA_pos : 0 < p.prob / (1 - p.prob) := div_pos p.h_pos (sub_pos_of_lt p.h_lt_one)
  have hB_pos : 0 < pi.prob / (1 - pi.prob) := div_pos pi.h_pos (sub_pos_of_lt pi.h_lt_one)
  exact log_div hA_pos.ne' hB_pos.ne'

end StrictBinaryState

end InfoGeometry.Canonical.ModularTheory
