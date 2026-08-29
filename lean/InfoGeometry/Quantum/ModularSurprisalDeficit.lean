/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ModularSurprisalDeficit

open Real

noncomputable section

/-!
# Modular Surprisal Deficit & Operator Convexity in Quantum Information Geometry

This module formalizes the non-negative scalar Bregman generator:
  f(x) = exp(-x) - 1 + x

which underlies the operator deficit:
  f(β K) = exp(-β K) - I + β K ≥ 0
-/

/-- The modular surprisal deficit function f(x) = exp(-x) - 1 + x. -/
def surprisalDeficit (x : ℝ) : ℝ :=
  Real.exp (-x) - 1 + x

/-!
### 1. Fundamental Properties of the Surprisal Deficit
-/

/-- 🏆 THEOREM 1 (Equilibrium Ground State):
    At the unperturbed equilibrium x = 0, the surprisal deficit vanishes: f(0) = 0. -/
theorem surprisal_deficit_zero :
    surprisalDeficit 0 = 0 := by
  unfold surprisalDeficit
  rw [neg_zero, Real.exp_zero]
  ring

/-- 🏆 THEOREM 2 (Non-Negativity / Klein Deficit Lower Bound):
    For all x ∈ ℝ, f(x) ≥ 0. -/
theorem surprisal_deficit_nonneg (x : ℝ) :
    0 ≤ surprisalDeficit x := by
  unfold surprisalDeficit
  have h := Real.add_one_le_exp (-x)
  linarith

/-- 🏆 THEOREM 3 (First Derivative / First Law Vanishing):
    The derivative of f(x) is -exp(-x) + 1, which vanishes at x = 0. -/
theorem hasDerivAt_surprisalDeficit (x : ℝ) :
    HasDerivAt surprisalDeficit (- Real.exp (-x) + 1) x := by
  have h_exp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (- Real.exp (-x)) x := by
    have h_neg : HasDerivAt (fun z : ℝ => -z) (-1) x := by
      simpa using (hasDerivAt_id x).neg
    have h_comp := (Real.hasDerivAt_exp (-x)).comp x h_neg
    simpa using h_comp
  have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have h_id : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have h_sub := h_exp.sub h_one
  have h_add := h_sub.add h_id
  unfold surprisalDeficit
  simpa using h_add

/-- 🏆 THEOREM 4 (Stationary Point at Equilibrium):
    The first-order linear variation vanishes at x = 0: f'(0) = 0. -/
theorem surprisal_deficit_deriv_at_zero :
    HasDerivAt surprisalDeficit 0 0 := by
  have h := hasDerivAt_surprisalDeficit 0
  have h_val : - Real.exp (-0) + 1 = 0 := by
    rw [neg_zero, Real.exp_zero]
    ring
  rw [h_val] at h
  exact h

/-!
### 2. Grand Capstone: Modular Surprisal Deficit Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Full synthesis of the surprisal deficit non-negativity,
    equilibrium vanishing, and first-law saturation at x = 0 -/
theorem grand_surprisal_deficit_synthesis (x : ℝ) :
    (surprisalDeficit 0 = 0) ∧
    (0 ≤ surprisalDeficit x) ∧
    (HasDerivAt surprisalDeficit 0 0) :=
  ⟨surprisal_deficit_zero,
   surprisal_deficit_nonneg x,
   surprisal_deficit_deriv_at_zero⟩

end

end InfoGeometry.Quantum.ModularSurprisalDeficit
