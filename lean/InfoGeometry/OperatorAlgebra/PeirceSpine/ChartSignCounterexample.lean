/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A rational matrix obstruction to the early chart formula

The cut and both off-diagonal generators are native `2 × 2` rational
matrices. They satisfy the actual Peirce support equations. The early
candidate `P + (a+b) + ab - (ab+ba)a` is not idempotent, and reversing the
two shear factors changes the genuine conjugate. This is a finite matrix
counterexample to the conflicting formula, not a statement about a manifold.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ChartSignCounterexample

open Matrix

abbrev Mat := Matrix (Fin 2) (Fin 2) ℚ

def cut : Mat := !![1, 0; 0, 0]
def upper : Mat := !![0, 1; 0, 0]
def lower : Mat := !![0, 0; 1, 0]

/-- The rational matrix units realize an idempotent cut and its two
opposite Peirce corners. -/
theorem matrix_units_peirce_support :
    cut * cut = cut ∧ conePlus cut upper = upper ∧ coneMinus cut lower = lower := by
  refine ⟨?_, ?_, ?_⟩ <;>
    apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [cut, upper, lower, conePlus, coneMinus,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- The opposite corner generators do not commute in the actual matrix ring. -/
theorem upper_lower_noncommute : upper * lower ≠ lower * upper := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The source's early proposed dressed expression. Its factor order is
kept exactly as supplied. -/
def earlyClaim : Mat :=
  cut + (upper + lower) + upper * lower - (upper * lower + lower * upper) * upper

/-- The `(0,0)` entries of the proposed expression and its square are
respectively `2` and `4`, so the proposed expression is not idempotent. -/
theorem early_claim_not_idempotent : earlyClaim * earlyClaim ≠ earlyClaim := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [earlyClaim, cut, upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The opposite ordered conjugations have distinct `(0,0)` entries.
Both are actual products of matrices, not scalar stand-ins. -/
theorem opposite_conjugations_ne :
    (1 + upper) * (cut + lower) * (1 - upper) ≠
      (1 - upper) * (cut + lower) * (1 + upper) := by
  intro h
  have h00 := congrArg (fun M : Mat => M 0 0) h
  norm_num [cut, upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.OperatorAlgebra.PeirceSpine.ChartSignCounterexample
