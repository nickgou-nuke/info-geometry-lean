/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InfoGeometry.Canonical.DrazinShellPeirce
import InfoGeometry.Canonical.DrazinShellMatrixAction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact operator counterexamples to overstrong prose in the two source notes. -/
namespace InfoGeometry.Canonical.PeirceSquareZeroExamples

open Matrix
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

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

/-- Even a self-adjoint Drazin projector need not be central in the ambient ring. -/
theorem drazin_projection_not_central :
    ∃ a d : Matrix (Fin 2) (Fin 2) ℝ, IsDrazinInverse a d 1 ∧
      ¬ (∀ x, projection a d * x = x * projection a d) := by
  let p : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
  have hp : p * p = p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [p, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨p, p, IsDrazinInverse.of_idempotent hp, ?_⟩
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1)
    (h !![0,1;0,0])
  norm_num [projection, p, Matrix.mul_apply, Fin.sum_univ_succ] at he

open InfoGeometry.Canonical.DrazinShellMatrixAction
open InfoGeometry.Canonical.DrazinShellPeirce
open InfoGeometry.Canonical.DrazinObliqueShellResolution

/-- A nonzero corner of the existing oblique example is its actual nilpotent part. -/
theorem oblique_corner_eq :
    shellCorner obliqueA obliqueD obliquePowers 1 0 = obliqueN := by
  unfold shellCorner
  rw [oblique_shell_one, oblique_shell_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueA, obliqueN, Matrix.mul_apply, Fin.sum_univ_succ]

theorem oblique_corner_mp :
    IsMoorePenroseInverse (shellCorner obliqueA obliqueD obliquePowers 1 0) obliqueM := by
  rw [oblique_corner_eq]
  exact oblique_mp

/-- Concrete use of the general grading theorem on the actual shell corner. -/
theorem oblique_corner_grading_cube :
    let c := shellCorner obliqueA obliqueD obliquePowers 1 0
    (c * obliqueM - obliqueM * c) * (c * obliqueM - obliqueM * c) *
      (c * obliqueM - obliqueM * c) = c * obliqueM - obliqueM * c := by
  exact InfoGeometry.Singular.MoorePenroseSquareZero.grading_cube oblique_corner_mp
    (shellCorner_square_zero oblique_drazin oblique_mp_family (by decide : 1 ≠ 0))

/-- An oblique shell pair does not force its MP inverse into the reverse corner. -/
theorem oblique_inverse_not_reverse_corner :
    dressedShell obliqueA obliqueD obliquePowers 0 * obliqueM *
      dressedShell obliqueA obliqueD obliquePowers 1 ≠ obliqueM := by
  rw [oblique_shell_zero, oblique_shell_one]
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [obliqueM, Matrix.mul_apply, Fin.sum_univ_succ] at he

end
end InfoGeometry.Canonical.PeirceSquareZeroExamples
