import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfoGeometry.Canonical

open Real

/-- The logit function logit(x) = log(x / (1 - x)) -/
noncomputable def logit (x : ℝ) : ℝ :=
  log (x / (1 - x))

/-- The classical relative modular operator Delta_+ and Delta_- for binary states. -/
noncomputable def Delta_plus (r α : ℝ) : ℝ := r / α
noncomputable def Delta_minus (r α : ℝ) : ℝ := (1 - r) / (1 - α)

/-- The relative surprisal operators K_+ and K_- -/
noncomputable def rel_K_plus (r α : ℝ) : ℝ := - log (Delta_plus r α)
noncomputable def rel_K_minus (r α : ℝ) : ℝ := - log (Delta_minus r α)

/-- Theorem: The logit evidence gap is the spectral gap of the relative modular operator -/
theorem logit_gap_eq_spectral_gap (r α : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hα0 : 0 < α) (hα1 : α < 1) :
    logit r - logit α = rel_K_minus r α - rel_K_plus r α := by
  dsimp [logit, rel_K_minus, rel_K_plus, Delta_plus, Delta_minus]
  have h_r : log (r / (1 - r)) = log r - log (1 - r) := log_div hr0.ne' (sub_pos.mpr hr1).ne'
  have h_α : log (α / (1 - α)) = log α - log (1 - α) := log_div hα0.ne' (sub_pos.mpr hα1).ne'
  have h_D_p : log (r / α) = log r - log α := log_div hr0.ne' hα0.ne'
  have h_D_m : log ((1 - r) / (1 - α)) = log (1 - r) - log (1 - α) := log_div (sub_pos.mpr hr1).ne' (sub_pos.mpr hα1).ne'
  rw [h_r, h_α, h_D_p, h_D_m]
  ring

end InfoGeometry.Canonical
