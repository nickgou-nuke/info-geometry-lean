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
  rcases hz with ⟨hz0, hz1⟩
  have hsq_pos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hz0
  have hsq_lt_one : ‖z‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg z]
  have hlog : Real.log (‖z‖ ^ 2) ≠ 0 := by
    exact ne_of_lt (Real.log_neg hsq_pos hsq_lt_one)
  have hden : 0 < ‖z‖ ^ 2 * (Real.log (‖z‖ ^ 2)) ^ 2 :=
    mul_pos hsq_pos (sq_pos_of_ne_zero hlog)
  exact one_div_pos.mpr hden
