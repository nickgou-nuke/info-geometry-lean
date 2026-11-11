/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.RealDoubledIdealMetric
import InfoGeometry.Physics.KreinDiracBlock

/-!
# Real matrix counterexamples for overstrong Krein ideal claims

These are finite exact witnesses. They separate a null ideal generator from
an isotropic ideal, and an algebraic involution from a positive metric.
The generic positive-colimit theorems have their own explicit hypotheses.
-/

namespace InfoGeometry.Examples.RealKreinIdealCounterexamples

open Matrix InfoGeometry.Physics
open InfoGeometry.Canonical.SpinorialCore.Krein
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open InfoGeometry.Physics.KreinDiracBlock

def chiralIdempotent : BdGBlock ℝ := !![1, 0; 0, 0]

def idealVector : BdGBlock ℝ := !![1, 0; 1, 0]

theorem chiralIdempotent_sq : chiralIdempotent * chiralIdempotent = chiralIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralIdempotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralIdempotent_sharp_complement :
    sharp andreevSwap chiralIdempotent = 1 - chiralIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sharp, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] <;>
    norm_num [andreevSwap, chiralIdempotent]

theorem chiralIdempotent_null : sharp andreevSwap chiralIdempotent * chiralIdempotent = 0 := by
  rw [chiralIdempotent_sharp_complement, sub_mul, one_mul, chiralIdempotent_sq, sub_self]

theorem idealVector_supported : idealVector * chiralIdempotent = idealVector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [idealVector, chiralIdempotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The null generator does not make every Gram value of its ideal zero. -/
theorem idealVector_sharp_gram_ne_zero : sharp andreevSwap idealVector * idealVector ≠ 0 := by
  intro h
  have h10 := congrArg (fun X : BdGBlock ℝ => X 1 0) h
  simp only [sharp, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] at h10
  norm_num [andreevSwap, idealVector] at h10

theorem idealVector_sharp_gram_sq_zero :
    (sharp andreevSwap idealVector * idealVector) ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pow_two, sharp, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] <;>
    norm_num [andreevSwap, idealVector]

theorem idealVector_sharp_density_zero : idealVector * sharp andreevSwap idealVector = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sharp, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two] <;>
    norm_num [andreevSwap, idealVector]

/-- An involution with unit squared gap can still give a negative twisted form. -/
theorem negative_grading_square :
    (-chiralGrading : BdGBlock ℝ) * (-chiralGrading) = 1 := by
  simpa only [neg_mul, mul_neg, neg_neg] using chiralGrading_sq (A := ℝ)

theorem negative_grading_twisted_value :
    bilinear (chiralGrading : BdGBlock ℝ) (-chiralGrading) ![1, 0] ![1, 0] = -1 := by
  norm_num [bilinear, diracRow, chiralGrading, Matrix.vecMul, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- With full real matrix coefficients, both proposed diagonal horizon
equations hold while the off-diagonal commutator obstructs square zero. -/
theorem horizon_diagonals_do_not_imply_square_zero :
    let m : BdGBlock ℝ := chiralGrading
    let b : BdGBlock ℝ := andreevSwap
    m * m = b * star b ∧ m * m = star b * b ∧
      diracBlock m b * diracBlock m b ≠ 0 := by
  dsimp only
  have hb : star (andreevSwap (A := ℝ)) = andreevSwap := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [andreevSwap]
  refine ⟨?_, ?_, ?_⟩
  · rw [hb, chiralGrading_sq, andreevSwap_sq]
  · rw [hb, chiralGrading_sq, andreevSwap_sq]
  · rw [diracBlock_sq]
    intro h
    have hentry := congrArg (fun X : BdGBlock (BdGBlock ℝ) => X 0 1 0 1) h
    norm_num [chiralGrading, andreevSwap, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The normalization itself leaves the sign of the twisted metric open. -/
theorem negative_mass_normalized_metric :
    chiralGrading *
      normalizeByUnit (diracBlock (-1 : ℝ) 0) (1 : (BdGBlock ℝ)ˣ) =
        -(1 : BdGBlock ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizeByUnit, diracBlock, chiralGrading, Matrix.mul_apply,
      Fin.sum_univ_two]

end InfoGeometry.Examples.RealKreinIdealCounterexamples
