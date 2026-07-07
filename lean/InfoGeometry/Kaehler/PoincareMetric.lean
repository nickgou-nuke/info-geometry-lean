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

lemma poincare_norm_sq_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < ‖z‖ ^ 2 := by
  exact sq_pos_of_pos hz.1

lemma poincare_log_sq_pos {z : ℂ} (hz : z ∈ PuncturedDisc) :
    0 < (Real.log (‖z‖ ^ 2)) ^ 2 := by
  have hlog_ne_zero : Real.log (‖z‖ ^ 2) ≠ 0 := by
    intro hlog
    rcases Real.log_eq_zero.mp hlog with h0 | h1 | hneg1
    · have hsq_nonneg : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
      linarith [poincare_norm_sq_pos hz]
    · have hsq_lt_one : ‖z‖ ^ 2 < 1 := by
        have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
        nlinarith [hz.2, hz_nonneg]
      have hneq : ‖z‖ ^ 2 ≠ 1 := by
        intro h'
        rw [h'] at hsq_lt_one
        norm_num at hsq_lt_one
      exact hneq h1
    · have hsq_nonneg : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
      linarith [poincare_norm_sq_pos hz]
  exact sq_pos_of_ne_zero hlog_ne_zero

lemma poincareDensity_pos {z : ℂ} (hz : z ∈ PuncturedDisc) : 0 < poincareDensity z := by
  unfold poincareDensity
  exact one_div_pos.mpr (mul_pos (poincare_norm_sq_pos hz) (poincare_log_sq_pos hz))
