/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Core.TripotentDefect
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.NCG.TripotentMatrixGeometry
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

/-!
# A dense real tripotent in the full four-by-four matrix algebra

A symmetric orthogonal matrix transports all sixteen matrix units. Their
products retain the full matrix multiplication law. The tripotent has three
nonzero spectral sectors, every one of its entries is nonzero, and its zero
weight contains a noncommutative two-by-two corner.
-/

noncomputable section

namespace InfoGeometry.Canonical.TripotentMatrixExample

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Physics.Algebra

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

/-- The Householder reflection for the vector `(1,2,3,4)`. -/
def reflection : Mat :=
  !![14/15, -(2/15), -(3/15), -(4/15);
     -(2/15), 11/15, -(6/15), -(8/15);
     -(3/15), -(6/15), 6/15, -(12/15);
     -(4/15), -(8/15), -(12/15), -(1/15)]

theorem reflection_sq : reflection * reflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem reflection_selfAdjoint : IsSelfAdjoint reflection := by
  change star reflection = reflection
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem reflection_entry_ne_zero (i j : Fin 4) : reflection i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [reflection]

/-- Full matrix units expressed in a dense orthonormal frame. -/
def frameUnit (i j : Fin 4) : Mat := reflection * Matrix.single i j 1 * reflection

theorem frameUnit_apply (i j a b : Fin 4) :
    frameUnit i j a b = reflection a i * reflection j b := by
  unfold frameUnit
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne 1 i j a k hk reflection, zero_mul]
  · simp

theorem frameUnit_entry_ne_zero (i j a b : Fin 4) : frameUnit i j a b ≠ 0 := by
  rw [frameUnit_apply]
  exact mul_ne_zero (reflection_entry_ne_zero a i) (reflection_entry_ne_zero j b)

theorem frameUnit_ne_zero (i j : Fin 4) : frameUnit i j ≠ 0 := by
  intro h
  exact frameUnit_entry_ne_zero i j 0 0 (congrArg (fun X : Mat => X 0 0) h)

theorem reflection_sandwich_mul (A B : Mat) :
    (reflection * A * reflection) * (reflection * B * reflection) =
      reflection * (A * B) * reflection := by
  calc
    _ = reflection * A * (reflection * reflection) * B * reflection := by
      simp only [mul_assoc]
    _ = _ := by rw [reflection_sq]; simp only [mul_one, mul_assoc]

/-- The transported units retain the full matrix multiplication law. -/
theorem frameUnit_mul (i j k l : Fin 4) :
    frameUnit i j * frameUnit k l = if j = k then frameUnit i l else 0 := by
  unfold frameUnit
  rw [reflection_sandwich_mul]
  split_ifs with h
  · subst k
    simp only [Matrix.single_mul_single_same, one_mul]
  · rw [Matrix.single_mul_single_of_ne 1 i j k h 1]
    simp only [mul_zero, zero_mul]

theorem frameUnit_star (i j : Fin 4) : star (frameUnit i j) = frameUnit j i := by
  simp only [frameUnit, star_mul, reflection_selfAdjoint.star_eq, mul_assoc]
  congr 2
  ext a b
  simp [Matrix.single, and_comm]

/-- The difference of two orthogonal dense-frame idempotents. -/
def tripotent : Mat := frameUnit 0 0 - frameUnit 1 1

theorem tripotent_cube : tripotent * tripotent * tripotent = tripotent := by
  exact (orthogonal_difference_powers
    (by simp [IsIdempotentElem, frameUnit_mul] : IsIdempotentElem (frameUnit 0 0))
    (by simp [IsIdempotentElem, frameUnit_mul] : IsIdempotentElem (frameUnit 1 1))
    (by simp [frameUnit_mul]) (by simp [frameUnit_mul])).2

theorem tripotent_selfAdjoint : IsSelfAdjoint tripotent := by
  change star tripotent = tripotent
  simp only [tripotent, star_sub, frameUnit_star]

theorem tripotent_entry_ne_zero (i j : Fin 4) : tripotent i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [tripotent, Matrix.sub_apply, frameUnit_apply, reflection]

theorem projPos_eq : projPos tripotent = frameUnit 0 0 := by
  exact InfoGeometry.Core.TripotentDefect.projPos_sub_of_orthogonal
    (by simp [frameUnit_mul]) (by simp [frameUnit_mul])
    (by simp [frameUnit_mul]) (by simp [frameUnit_mul])

theorem projNeg_eq : projNeg tripotent = frameUnit 1 1 := by
  exact InfoGeometry.Core.TripotentDefect.projNeg_sub_of_orthogonal
    (by simp [frameUnit_mul]) (by simp [frameUnit_mul])
    (by simp [frameUnit_mul]) (by simp [frameUnit_mul])

/-- The zero sector contains two independent diagonal units in the dense frame. -/
theorem projZero_eq : projZero tripotent = frameUnit 2 2 + frameUnit 3 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projZero, tripotent, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, frameUnit_apply, reflection]

def weight : Fin 4 → ℝ := ![1, -1, 0, 0]

theorem ad_frameUnit (i j : Fin 4) :
    LieAlgebra.ad ℝ Mat tripotent (frameUnit i j) =
      (weight i - weight j) • frameUnit i j := by
  change tripotent * frameUnit i j - frameUnit i j * tripotent = _
  fin_cases i <;> fin_cases j <;>
    simp [tripotent, sub_mul, mul_sub, frameUnit_mul, weight] <;> module

/-- The generator acts nontrivially on the full algebra. -/
theorem tripotent_noncommute :
    tripotent * frameUnit 0 1 ≠ frameUnit 0 1 * tripotent := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 0) h
  norm_num [tripotent, sub_mul, mul_sub, frameUnit_mul,
    Matrix.sub_apply, frameUnit_apply, reflection] at hc

/-- Two dense self-adjoint matrices in this frame fail to commute. -/
theorem reflection_tripotent_noncommute :
    reflection * tripotent ≠ tripotent * reflection := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 1) h
  norm_num [tripotent, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.sub_apply, frameUnit_apply, reflection] at hc

theorem zero_weight_forward : LieAlgebra.ad ℝ Mat tripotent (frameUnit 2 3) = 0 := by
  simpa [weight] using ad_frameUnit 2 3

theorem zero_weight_reverse : LieAlgebra.ad ℝ Mat tripotent (frameUnit 3 2) = 0 := by
  simpa [weight] using ad_frameUnit 3 2

/-- Grade zero is not forced to be an abelian Lie algebra. -/
theorem zero_weight_noncommute :
    frameUnit 2 3 * frameUnit 3 2 ≠ frameUnit 3 2 * frameUnit 2 3 := by
  intro h
  have hc := congrArg (fun X : Mat => X 0 0) h
  norm_num [frameUnit_mul, frameUnit_apply, reflection] at hc

/-- Every allowed weight occurs on a nonzero, dense matrix in the full algebra. -/
theorem all_five_weights_occur (k : FiveGrade) :
    ∃ X : Mat, X ≠ 0 ∧
      X ∈ (LieAlgebra.ad ℝ Mat tripotent).eigenspace (fiveGradeValue k : ℝ) := by
  cases k with
  | negTwo =>
      refine ⟨frameUnit 1 0, frameUnit_ne_zero 1 0, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      convert ad_frameUnit 1 0 using 1
      norm_num [weight, fiveGradeValue]
  | negOne =>
      refine ⟨frameUnit 2 0, frameUnit_ne_zero 2 0, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa [weight, fiveGradeValue] using ad_frameUnit 2 0
  | zero =>
      refine ⟨frameUnit 2 3, frameUnit_ne_zero 2 3, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa [weight, fiveGradeValue] using ad_frameUnit 2 3
  | posOne =>
      refine ⟨frameUnit 0 2, frameUnit_ne_zero 0 2, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa [weight, fiveGradeValue] using ad_frameUnit 0 2
  | posTwo =>
      refine ⟨frameUnit 0 1, frameUnit_ne_zero 0 1, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      convert ad_frameUnit 0 1 using 1
      norm_num [weight, fiveGradeValue]

/-- In this concrete full algebra, none of the five owned summands vanishes. -/
theorem fiveGradeRange_ne_bot (k : FiveGrade) : fiveGradeRange tripotent k ≠ ⊥ := by
  intro h
  obtain ⟨X, hX, hmem⟩ := all_five_weights_occur k
  rw [← InfoGeometry.Core.TripotentAdjoint.fiveGradeRange_eq_eigenspace tripotent_cube k,
    h] at hmem
  exact hX ((Submodule.mem_bot ℝ).mp hmem)

/-- The same tripotent defines a genuine self-adjoint matrix generalized inverse. -/
theorem tripotent_self_moorePenrose :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse tripotent tripotent :=
  InfoGeometry.NCG.TripotentMatrixGeometry.self_moorePenrose_of_isSelfAdjoint
    tripotent_cube tripotent_selfAdjoint

end InfoGeometry.Canonical.TripotentMatrixExample
