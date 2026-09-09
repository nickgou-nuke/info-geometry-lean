import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.QuantumFluctuations

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def primePhaseHarmonic (p : ℕ) (m : ℕ) (E : ℝ) : ℝ :=
  (1 / Real.pi) * (Real.sin (E * (m : ℝ) * Real.log (p : ℝ)) / ((m : ℝ) * Real.rpow (p : ℝ) ((m : ℝ) / 2)))

def selbergVariance (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi ^ 2)) * Real.log (Real.log T)

theorem prime_phase_harmonic_at_zero (p : ℕ) (m : ℕ) :
    primePhaseHarmonic p m 0 = 0 := by
  unfold primePhaseHarmonic
  have : (0 : ℝ) * (m : ℝ) * Real.log (p : ℝ) = 0 := by ring
  rw [this, Real.sin_zero, zero_div, mul_zero]

theorem prime_phase_harmonic_odd (p : ℕ) (m : ℕ) (E : ℝ) :
    primePhaseHarmonic p m (-E) = - primePhaseHarmonic p m E := by
  unfold primePhaseHarmonic
  have : -E * (m : ℝ) * Real.log (p : ℝ) = - (E * (m : ℝ) * Real.log (p : ℝ)) := by ring
  rw [this, Real.sin_neg, neg_div, mul_neg]

theorem selberg_variance_pos (T : ℝ) (hT : Real.exp 1 < T) :
    0 < selbergVariance T := by
  unfold selbergVariance
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_T_pos : 0 < T := lt_trans h_exp_pos hT
  have h1 : 1 < Real.log T := (Real.lt_log_iff_exp_lt h_T_pos).mpr hT
  have h2 : 0 < Real.log (Real.log T) := Real.log_pos h1
  have h_pi : 0 < 2 * Real.pi ^ 2 := by
    have hp := Real.pi_pos
    positivity
  exact mul_pos (one_div_pos.mpr h_pi) h2
