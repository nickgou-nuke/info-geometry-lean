/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinMPCartan
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

/-!
# Noncommutative witnesses and characteristic-two boundary

The general operators remain in the abstract ring owners. These exact matrix
instances show that their hypotheses and distinctions are substantive.
-/

namespace InfoGeometry.Canonical.CartanDrazinMPExamples

open Matrix
open InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinMPCartan
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.MetricAlgebraicProjectionDefect

/-- An oblique idempotent with a nonzero metric/spectral mismatch. -/
def oblique : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

/-- Its actual Moore--Penrose inverse, not its Drazin inverse. -/
noncomputable def obliqueMP : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 0; 1 / 2, 0]

theorem oblique_idempotent : oblique * oblique = oblique := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_two]

theorem oblique_drazin : IsDrazinInverse oblique oblique 1 :=
  IsDrazinInverse.of_idempotent oblique_idempotent

theorem oblique_mp : IsMoorePenroseInverse oblique obliqueMP := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [oblique, obliqueMP, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem oblique_nilpotent_zero : fittingNilpotentPart oblique oblique = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fittingNilpotentPart, complementaryProjection, projection,
      oblique, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem oblique_left_anomaly :
    leftAnomaly oblique oblique obliqueMP = !![0, -1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftAnomaly, commutatorDefect, projection, oblique, obliqueMP,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem oblique_left_anomaly_nonzero : leftAnomaly oblique oblique obliqueMP ≠ 0 := by
  rw [oblique_left_anomaly]
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num at he

/-- A general MP support difference has no unconditional tripotence theorem. -/
theorem oblique_mp_difference_not_tripotent :
    let g := obliqueMP * oblique - oblique * obliqueMP
    g * g * g ≠ g := by
  dsimp
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [oblique, obliqueMP, Matrix.mul_apply, Fin.sum_univ_two] at he

/-- A projection and a nonzero odd sum used to exercise the feedback loop. -/
def diagonalSeed : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

def swapSeed : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem diagonalSeed_idempotent : diagonalSeed * diagonalSeed = diagonalSeed := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalSeed, Matrix.mul_apply, Fin.sum_univ_two]

/-- The sum of directed square-zero corners need not be square-zero. -/
theorem odd_sum_squares_to_one :
    oddPart diagonalSeed swapSeed = swapSeed ∧ swapSeed * swapSeed = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [oddPart, component10, component01, complementIdempotent,
      diagonalSeed, swapSeed, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply]

theorem concrete_corner_mp :
    IsMoorePenroseInverse (component10 diagonalSeed swapSeed)
      (component01 diagonalSeed swapSeed) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [component10, component01, complementIdempotent, diagonalSeed, swapSeed,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- Execute the return from a directed corner to a new star projection/reflection. -/
theorem concrete_corner_feedback :
    let c := component10 diagonalSeed swapSeed
    let b := component01 diagonalSeed swapSeed
    IsStarProjection (c * b) ∧ b * b = 0 ∧
      reflection (c * b) * reflection (c * b) = 1 :=
  corner_to_new_reflection diagonalSeed_idempotent concrete_corner_mp

/-- In characteristic two the reflection cannot recover the Peirce grading. -/
theorem characteristicTwo_reflection_boundary :
    let p : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 0, 0]
    let x : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    p * p = p ∧ reflection p = 1 ∧ x ≠ 0 ∧
      evenPart p x = 0 ∧ oddPart p x = x ∧ reflection p * x * reflection p = x := by
  decide

#check @drazin_mp_joint_cartan_synthesis
#check @anomaly_identities
#check @squareZero_mp_to_reflection
#check @leftAnomaly_eq_neg_projectionDefect
#check @reflectionConj
#check @sign_eigenspaces
#check @multiplication_rules
#check @decomposition_unique

end InfoGeometry.Canonical.CartanDrazinMPExamples
