/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import InfoGeometry.Quantum.PrimonColimitFiltration

namespace InfoGeometry.Quantum.PrimonThermodynamics

open Real
open InfoGeometry.Quantum.PrimonColimit

noncomputable section

/-- Mean bosonic energy of prime mode p at inverse temperature β:
    E^{(p)}(β) = ln(p) / (p^β - 1). -/
def primeMeanEnergy (p : ℕ) (beta : ℝ) : ℝ :=
  Real.log (p : ℝ) / ((p : ℝ) ^ beta - 1)

/-!
### 1. Differentiability of the Boltzmann Factor $p^{-\beta}$
-/

/-- Derivative of the mode Boltzmann factor:
    d/dβ [ p^(-β) ] = -ln(p) * p^(-β). -/
theorem hasDerivAt_prime_boltzmann (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) :
    HasDerivAt (fun b : ℝ => (p : ℝ) ^ (-b)) (-Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) beta := by
  have hp_pos : 0 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have h_exp : (fun b : ℝ => (p : ℝ) ^ (-b)) = (fun b : ℝ => Real.exp (-Real.log (p : ℝ) * b)) := by
    ext b
    rw [Real.rpow_def_of_pos hp_pos]
    ring_nf
  rw [h_exp]
  have h_inner : HasDerivAt (fun b : ℝ => -Real.log (p : ℝ) * b) (-Real.log (p : ℝ)) beta := by
    have h_id : HasDerivAt (fun b : ℝ => b) 1 beta := hasDerivAt_id beta
    have h_mul := h_id.const_mul (-Real.log (p : ℝ))
    simpa using h_mul
  have h_deriv := HasDerivAt.exp h_inner
  have h_eq_eval : Real.exp (-Real.log (p : ℝ) * beta) = (p : ℝ) ^ (-beta) := by
    rw [Real.rpow_def_of_pos hp_pos]
    ring_nf
  have h_prod : Real.exp (-Real.log (p : ℝ) * beta) * -Real.log (p : ℝ) = -Real.log (p : ℝ) * (p : ℝ) ^ (-beta) := by
    rw [h_eq_eval]
    ring
  rw [h_prod] at h_deriv
  exact h_deriv

/-!
### 2. Derivative of the Single-Mode Surprisal Potential
-/

/-- 🏆 THEOREM: The derivative of the surprisal potential satisfies
    d/dβ [ ψ^{(p)}(β) ] = - E^{(p)}(β) = - ln(p) / (p^β - 1). -/
theorem hasDerivAt_prime_surprisal_potential (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    HasDerivAt (fun b : ℝ => primeSurprisalPotential p b) (-primeMeanEnergy p beta) beta := by
  have hp_pos : 0 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have hp_gt_one : 1 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have h_neg : -beta < 0 := by linarith
  have h_lt_one : (p : ℝ) ^ (-beta) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt_one h_neg
  have h_denom_pos : 0 < 1 - (p : ℝ) ^ (-beta) := by linarith
  have h_denom_ne : 1 - (p : ℝ) ^ (-beta) ≠ 0 := ne_of_gt h_denom_pos

  -- Express ψ^{(p)}(b) as -ln(1 - p^(-b)) globally
  have h_eq : (fun b : ℝ => primeSurprisalPotential p b) = (fun b : ℝ => -Real.log (1 - (p : ℝ) ^ (-b))) := by
    ext b
    unfold primeSurprisalPotential primeEulerFactor
    rw [Real.log_inv]
  rw [h_eq]

  have h_boltz_deriv := hasDerivAt_prime_boltzmann p hp beta
  have h_diff : HasDerivAt (fun b : ℝ => 1 - (p : ℝ) ^ (-b))
      (Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) beta := by
    have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 beta := hasDerivAt_const beta 1
    have h_sub := h_const.sub h_boltz_deriv
    have h_ring : 0 - (-Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) = Real.log (p : ℝ) * (p : ℝ) ^ (-beta) := by ring
    rw [h_ring] at h_sub
    exact h_sub

  have h_log_comp := HasDerivAt.log h_diff h_denom_ne
  have h_neg_log := h_log_comp.neg

  -- Algebraic simplification to -ln(p) / (p^β - 1)
  have h_alg : -(Real.log (p : ℝ) * (p : ℝ) ^ (-beta) / (1 - (p : ℝ) ^ (-beta))) = -primeMeanEnergy p beta := by
    unfold primeMeanEnergy
    have h_pow_pos : 0 < (p : ℝ) ^ beta := Real.rpow_pos_of_pos hp_pos beta
    have h_rewr : (1 - (p : ℝ) ^ (-beta)) * (p : ℝ) ^ beta = (p : ℝ) ^ beta - 1 := by
      rw [sub_mul, one_mul, ← Real.rpow_add hp_pos]
      have h_zero : -beta + beta = 0 := by ring
      rw [h_zero, Real.rpow_zero]
    have h_mult : (Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) / (1 - (p : ℝ) ^ (-beta)) =
        (Real.log (p : ℝ) * (p : ℝ) ^ (-beta) * (p : ℝ) ^ beta) / ((1 - (p : ℝ) ^ (-beta)) * (p : ℝ) ^ beta) := by
      rw [mul_div_mul_right _ _ (ne_of_gt h_pow_pos)]
    rw [h_mult, h_rewr]
    have h_num : Real.log (p : ℝ) * (p : ℝ) ^ (-beta) * (p : ℝ) ^ beta = Real.log (p : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hp_pos]
      have h_zero : -beta + beta = 0 := by ring
      rw [h_zero, Real.rpow_zero, mul_one]
    rw [h_num]

  rw [h_alg] at h_neg_log
  exact h_neg_log

/-!
### 3. Thermodynamic Mean Mode Energy Relation
-/

/-- The mean mode energy is the negative gradient of the surprisal potential:
    E^{(p)}(β) = - d/dβ [ ψ^{(p)}(β) ]. -/
theorem prime_mean_energy_eq_neg_deriv (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    deriv (fun b : ℝ => primeSurprisalPotential p b) beta = -primeMeanEnergy p beta :=
  (hasDerivAt_prime_surprisal_potential p hp beta h_beta).deriv

/-- Strict positivity of the mean mode energy for β > 0 and prime p ≥ 2. -/
theorem prime_mean_energy_pos (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    0 < primeMeanEnergy p beta := by
  unfold primeMeanEnergy
  have hp_gt_one : 1 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
    linarith
  have h_log_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt_one
  have h_pow_gt_one : 1 < (p : ℝ) ^ beta := Real.one_lt_rpow hp_gt_one h_beta
  have h_denom_pos : 0 < (p : ℝ) ^ beta - 1 := by linarith
  exact div_pos h_log_pos h_denom_pos

end

end InfoGeometry.Quantum.PrimonThermodynamics
