/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Scalar spectral-gap bounds

This module proves the finite-mode inequalities used for the arithmetic
Primon model. For an excited label n ≥ 2 and a positive real parameter s,
the weight n ^ (-s) is bounded by the first-excited weight 2 ^ (-s), and is
strictly smaller than one.

The file does not construct an infinite-dimensional Hamiltonian, a heat
semigroup, a trace-class operator, or a KMS state. The final two lemmas are
generic consequences of an explicitly supplied operator-norm estimate.
-/

open Complex Real

namespace InfoGeometry.Arithmetic.SpectralDistance

theorem primon_mode_decay_bound (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    (n : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hneg : -s ≤ 0 := by linarith
  exact Real.rpow_le_rpow_of_nonpos h2pos h2n hneg

theorem primon_mode_strict_contraction (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    (n : ℝ) ^ (-s) < 1 := by
  have h1n : (1 : ℝ) < (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnegs : -s < 0 := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg h1n hnegs

theorem primon_spectral_gap_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem primon_gap_decay_factor_lt_one (s : ℝ) (hs : 0 < s) :
    (2 : ℝ) ^ (-s) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem primon_gap_decay_factor_eq_exp (s : ℝ) :
    (2 : ℝ) ^ (-s) = Real.exp (-s * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

variable {H_space : Type*} [NormedAddCommGroup H_space] [NormedSpace ℂ H_space]
variable (flow : ℝ → (H_space →L[ℂ] H_space))

/-- A supplied operator-norm estimate gives the corresponding vector bound. -/
theorem vector_bound_of_flow_norm_bound (gap : ℝ) (s : ℝ) (v : H_space)
    (h_norm : ‖flow s‖ ≤ Real.exp (-s * gap)) :
    ‖flow s v‖ ≤ Real.exp (-s * gap) * ‖v‖ := by
  have h_op : ‖flow s v‖ ≤ ‖flow s‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm (flow s) v
  have h_nonneg : 0 ≤ ‖v‖ := norm_nonneg v
  nlinarith

/-- The vector bound specialized to the scalar gap log 2. -/
theorem primon_gas_strict_contraction (s : ℝ) (v : H_space)
    (h_norm : ‖flow s‖ ≤ Real.exp (-s * Real.log 2)) :
    ‖flow s v‖ ≤ (2 : ℝ) ^ (-s) * ‖v‖ := by
  have h_bound := vector_bound_of_flow_norm_bound flow (Real.log 2) s v h_norm
  rw [← primon_gap_decay_factor_eq_exp s] at h_bound
  exact h_bound

end InfoGeometry.Arithmetic.SpectralDistance
