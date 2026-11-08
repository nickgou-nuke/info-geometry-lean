/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.SquareZeroMoorePenrose
import InfoGeometry.Core.JordanAssociatorRing
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact operator counterexamples to overstrong prose in the two source notes. -/
namespace InfoGeometry.Canonical.PeirceSquareZeroExamples

open Matrix
open InfoGeometry.Singular.MoorePenrose

noncomputable section

def scaledStep : Matrix (Fin 2) (Fin 2) ℝ := !![0,2;0,0]
def reciprocalStep : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;1/2,0]

theorem scaledStep_square_zero : scaledStep * scaledStep = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [scaledStep, Matrix.mul_apply, Fin.sum_univ_succ]

theorem reciprocalStep_mp : IsMoorePenroseInverse scaledStep reciprocalStep := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [scaledStep, reciprocalStep, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [scaledStep, reciprocalStep, Matrix.mul_apply, Fin.sum_univ_succ]
  · change (scaledStep * reciprocalStep).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [scaledStep, reciprocalStep, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  · change (reciprocalStep * scaledStep).conjTranspose = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [scaledStep, reciprocalStep, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- d+d-dagger is not generally self-adjoint, despite having self-adjoint square. -/
theorem reciprocal_sum_not_selfAdjoint :
    ¬ IsSelfAdjoint (scaledStep + reciprocalStep) := by
  intro h
  change (scaledStep + reciprocalStep).conjTranspose = scaledStep + reciprocalStep at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [scaledStep, reciprocalStep, Matrix.conjTranspose_apply] at he

/-- Refutes the proposed universal triple identity using noncommuting matrix units. -/
theorem proposed_triple_identity_false :
    ¬ (∀ x y z : Matrix (Fin 2) (Fin 2) ℝ,
      x * y * z + z * y * x =
        (x * y) * z + z * (x * y) - (x * (z * y) - (z * y) * x)) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (h !![0,1;0,0] 1 !![0,0;1,0])
  norm_num [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ] at he

/-- The reciprocal is genuinely different from the adjoint, despite satisfying MP. -/
theorem reciprocalStep_ne_star_scaledStep : reciprocalStep ≠ star scaledStep := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
  norm_num [reciprocalStep, scaledStep, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at he

/-- The square of this non-self-adjoint sum is nevertheless a star projection. -/
theorem reciprocal_sum_square_isStarProjection :
    IsStarProjection ((scaledStep + reciprocalStep)^2) := by
  rw [reciprocalStep_mp.normalizedDirac_sq scaledStep_square_zero]
  exact reciprocalStep_mp.support_sum_isStarProjection scaledStep_square_zero

end
end InfoGeometry.Canonical.PeirceSquareZeroExamples
