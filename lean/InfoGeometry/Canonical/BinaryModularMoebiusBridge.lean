import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.ModularTheory

open Real

/-!
# Binary Relative Modular Operator and Möbius Bridge

This module formally extracts the Möbius evidence increment (the logit difference)
as the exact spectral gap of the relative modular surprisal operator for a binary state.
-/

/-- The standard logit function. -/
def logit (x : ℝ) : ℝ := log (x / (1 - x))

/-- 
A strict binary state space prior `pi = (prob, 1 - prob)`. 
We enforce 0 < prob < 1 to ensure invertibility and exact domain constraints.
-/
structure StrictBinaryState where
  prob : ℝ
  h_pos : 0 < prob
  h_lt_one : prob < 1

namespace StrictBinaryState

variable (pi p : StrictBinaryState)

/-- The positive modular eigenvalue Δ_+ = p / pi. -/
def deltaPlus : ℝ := p.prob / pi.prob

/-- The negative modular eigenvalue Δ_- = (1 - p) / (1 - pi). -/
def deltaMinus : ℝ := (1 - p.prob) / (1 - pi.prob)

theorem deltaPlus_pos : 0 < deltaPlus pi p := 
  div_pos p.h_pos pi.h_pos

theorem deltaMinus_pos : 0 < deltaMinus pi p := 
  div_pos (sub_pos_of_lt p.h_lt_one) (sub_pos_of_lt pi.h_lt_one)

/-- 
THEOREM: The Möbius evidence increment is the spectral gap 
of the relative modular surprisal operator.

log(Δ_+ / Δ_-) = logit(p) - logit(pi)
-/
theorem log_spectral_gap_eq_logit_diff :
    log (deltaPlus pi p / deltaMinus pi p) = logit p.prob - logit pi.prob := by
  dsimp [deltaPlus, deltaMinus, logit]
  -- Establish strict positivity for logarithms
  have h1 : p.prob / (1 - p.prob) > 0 := div_pos p.h_pos (sub_pos_of_lt p.h_lt_one)
  have h2 : pi.prob / (1 - pi.prob) > 0 := div_pos pi.h_pos (sub_pos_of_lt pi.h_lt_one)
  
  -- Rearrange the division algebraically
  have h_div_rearrange : (p.prob / pi.prob) / ((1 - p.prob) / (1 - pi.prob)) = 
      (p.prob / (1 - p.prob)) / (pi.prob / (1 - pi.prob)) := by
    -- In ℝ, a/b = a * b⁻¹. We rewrite to inverse multiplication to use `ring`.
    change (p.prob * pi.prob⁻¹) * ((1 - p.prob) * (1 - pi.prob)⁻¹)⁻¹ = 
           (p.prob * (1 - p.prob)⁻¹) * (pi.prob * (1 - pi.prob)⁻¹)⁻¹
    rw [mul_inv, inv_inv, mul_inv, inv_inv]
    ring
    
  rw [h_div_rearrange]
  exact log_div h1.ne' h2.ne'

end StrictBinaryState

end InfoGeometry.Canonical.ModularTheory
