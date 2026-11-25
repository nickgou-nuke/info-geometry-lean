/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import GaussianBlockSpin.WeightedCoarseGraining
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Positive, noncommuting coarse-graining example

The two precision matrices are proved positive definite. The covariance
calculation uses the actual inverses and exhibits the error caused by moving a
precision inverse through the averaging map.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining.Examples

open Matrix

def fineWeight : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]

def coarseWeight : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 3]

def averaging : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- The nondiagonal precision is strictly positive, including every real
nonzero vector, rather than only coordinate basis vectors. -/
theorem fineWeight_posDef : fineWeight.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [fineWeight]
  · intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_cases h0 : x 0 = 0
      · right
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      · exact Or.inl h0
    simp only [fineWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.star_apply, star_trivial, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rcases hx' with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (2 * x 0 + x 1)]

theorem coarseWeight_posDef : coarseWeight.PosDef := by
  have hd : (Matrix.diagonal ![(1 : ℝ), 3]).PosDef :=
    Matrix.PosDef.diagonal (by intro i; fin_cases i <;> norm_num)
  convert hd using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coarseWeight, Matrix.diagonal]

theorem fineWeight_inv : fineWeight⁻¹ = !![1, -1; -1, 2] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fineWeight, Matrix.mul_apply, Fin.sum_univ_two]

theorem coarseWeight_inv : coarseWeight⁻¹ = !![1, 0; 0, (1 / 3 : ℝ)] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coarseWeight, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two proved-positive precision matrices do not commute. -/
theorem weights_do_not_commute : fineWeight * coarseWeight ≠ coarseWeight * fineWeight := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [fineWeight, coarseWeight, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Moving the inverse precision through the averaging map changes the
transported covariance. The inverse is the same inverse used by the API. -/
theorem inverse_sandwich_order_matters :
    averaging * fineWeight⁻¹ * averagingᴴ ≠
      fineWeight⁻¹ * (averaging * averagingᴴ) := by
  rw [fineWeight_inv]
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [averaging, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h01

/-- Exact output of the general Woodbury theorem on the noncommuting input. -/
theorem coarsePrecision_inv_eq :
    (coarsePrecision fineWeight coarseWeight averaging)⁻¹ =
      !![2, 1; 1, (7 / 3 : ℝ)] := by
  rw [coarsePrecision_inv averaging fineWeight_posDef coarseWeight_posDef,
    fineWeight_inv, coarseWeight_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [averaging, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The effective precision in the example is strictly positive by the
general theorem, despite the failure of precision commutativity. -/
theorem coarsePrecision_example_posDef :
    (coarsePrecision fineWeight coarseWeight averaging).PosDef :=
  coarsePrecision_posDef averaging fineWeight_posDef coarseWeight_posDef

end GaussianBlockSpin.WeightedCoarseGraining.Examples
