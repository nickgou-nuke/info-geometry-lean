import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Metric Topology

/-- The punctured unit disc D^* in the complex plane. -/
def PuncturedDisc : Set ℂ := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1}

/-- The density function of the Poincaré metric on the punctured unit disc.
    Corresponds to the coefficient in ω_{D^*} = (i dz ∧ d z̄) / (|z|^2 (log |z|^2)^2). -/
noncomputable def poincareDensity (z : ℂ) : ℝ :=
  1 / (‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2)

lemma poincareDensity_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < poincareDensity z := by
  dsimp [poincareDensity]
  have hnorm_sq_pos : 0 < ‖z‖ ^ 2 := by
    exact sq_pos_of_pos hz.1
  have hnorm_sq_lt_one : ‖z‖ ^ 2 < 1 := by
    have h : ‖z‖ ^ 2 < (1 : ℝ) ^ 2 := by
      rw [sq_lt_sq]
      simpa [abs_of_nonneg (le_of_lt hz.1)] using hz.2
    simpa using h
  have hlog_neg : Real.log (‖z‖ ^ 2) < 0 := by
    exact Real.log_neg hnorm_sq_pos hnorm_sq_lt_one
  have hlog_sq_pos : 0 < (Real.log (‖z‖ ^ 2)) ^ 2 := by
    nlinarith [hlog_neg]
  have hden_pos : 0 < ‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2 := by positivity
  exact one_div_pos.mpr hden_pos
