/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# A real two-by-two fourth root of minus the identity

The operator is defined using the existing real Clifford matrix `Eminus`.
It is a matrix fourth root of `-1`, not a real scalar fourth root of `-1`.
Its failure to be symmetric is an explicit part of the result.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace InfoGeometry.Clifford.Cl11Matrix

def eighthRoot : Mat2 := (1 / Real.sqrt 2 : ℝ) • ((1 : Mat2) + Eminus)

private theorem inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem one_add_Eminus_sq :
    ((1 : Mat2) + Eminus) * ((1 : Mat2) + Eminus) = (2 : ℝ) • Eminus := by
  calc
    ((1 : Mat2) + Eminus) * ((1 : Mat2) + Eminus) =
        (1 : Mat2) + (2 : ℝ) • Eminus + Eminus * Eminus := by
      rw [two_smul]
      noncomm_ring
    _ = (2 : ℝ) • Eminus := by
      rw [Eminus_sq]
      simp only [neg_one_smul]
      abel

theorem eighthRoot_sq : eighthRoot ^ 2 = Eminus := by
  calc
    eighthRoot ^ 2 =
        ((1 / Real.sqrt 2 : ℝ) ^ 2) •
          (((1 : Mat2) + Eminus) * ((1 : Mat2) + Eminus)) := by
      simp only [eighthRoot, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • Eminus) := by
      rw [inv_sqrt_two_sq, one_add_Eminus_sq]
    _ = Eminus := by norm_num [smul_smul]

theorem eighthRoot_pow_four : eighthRoot ^ 4 = -(1 : Mat2) := by
  calc
    eighthRoot ^ 4 = (eighthRoot ^ 2) ^ 2 := by rw [← pow_mul]
    _ = Eminus ^ 2 := by rw [eighthRoot_sq]
    _ = -(1 : Mat2) := by simpa [pow_two] using Eminus_sq

theorem eighthRoot_pow_eight : eighthRoot ^ 8 = (1 : Mat2) := by
  calc
    eighthRoot ^ 8 = (eighthRoot ^ 4) ^ 2 := by rw [← pow_mul]
    _ = (-(1 : Mat2)) ^ 2 := by rw [eighthRoot_pow_four]
    _ = (1 : Mat2) := by simp

/-- A real matrix fourth root does not supply a symmetric scalar-sector solution. -/
theorem eighthRoot_not_symmetric : eighthRootᵀ ≠ eighthRoot := by
  intro h
  have h₀₁ := congrArg (fun A : Mat2 => A 0 1) h
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  simp [eighthRoot, Eminus, Matrix.transpose_apply] at h₀₁
  linarith

end InfoGeometry.Clifford.Cl11Matrix
