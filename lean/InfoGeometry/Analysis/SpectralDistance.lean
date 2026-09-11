import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-! Finite analytic spectral-gap and contraction readouts. -/

namespace InfoGeometry.Analysis.SpectralDistance

theorem primon_mode_decay_bound (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    (n : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hneg : -s ≤ 0 := by linarith
  exact Real.rpow_le_rpow_of_nonpos h2pos h2n hneg

theorem primon_mode_strict_contraction (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    (n : ℝ) ^ (-s) < 1 := by
  have h1n : (1 : ℝ) < (n : ℝ) := by
    have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnegs : -s < 0 := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg h1n hnegs

theorem primon_spectral_gap_pos : 0 < Real.log 2 := by
  have h1 : (1 : ℝ) < 2 := by norm_num
  exact Real.log_pos h1

class HasSpectralGap {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (flow : ℝ → (H →L[ℂ] H)) (gap : ℝ) : Prop where
  gap_pos : 0 < gap
  strict_contraction : ∀ s : ℝ, 0 < s → ‖flow s‖ ≤ Real.exp (-s * gap)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable (flow : ℝ → (H →L[ℂ] H))

theorem strict_contraction_of_spectral_flow (gap : ℝ) (h_gap : HasSpectralGap flow gap)
    (s : ℝ) (h_s : 0 < s) (v : H) :
    ‖flow s v‖ ≤ Real.exp (-s * gap) * ‖v‖ := by
  have h_norm := h_gap.strict_contraction s h_s
  have h_op : ‖flow s v‖ ≤ ‖flow s‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm (flow s) v
  have h_nonneg : 0 ≤ ‖v‖ := norm_nonneg v
  nlinarith

theorem primon_gas_strict_contraction (s : ℝ) (h_s : 0 < s) (v : H)
    (h_gap : HasSpectralGap flow (Real.log 2)) :
    ‖flow s v‖ ≤ (2 : ℝ) ^ (-s) * ‖v‖ := by
  have h_bound := strict_contraction_of_spectral_flow flow (Real.log 2) h_gap s h_s v
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h_exp : Real.exp (-s * Real.log 2) = (2 : ℝ) ^ (-s) := by
    rw [mul_comm, ← Real.rpow_def_of_pos h2pos]
  rw [h_exp] at h_bound
  exact h_bound

end InfoGeometry.Analysis.SpectralDistance
