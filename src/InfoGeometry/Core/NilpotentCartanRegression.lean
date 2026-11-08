/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.NilpotentToCartanDrazinMPPoset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Boundary and nonvacuity tests for the conditional Peirce development

These concrete examples refute overstrong extensions; they do not replace the
arbitrary-ring carriers of the main theorems. The endomorphism construction at
the end also works on modules of arbitrary dimension.
-/

namespace InfoGeometry.Core.NilpotentCartanRegression

open PeirceGrading
open InfoGeometry.Singular.MoorePenrose

/-- Square-zero does not imply the existence of an inner inverse. -/
theorem square_zero_without_inner_inverse :
    (2 : ZMod 4) * 2 = 0 ∧ ¬ ∃ b : ZMod 4, 2 * b * 2 = 2 := by decide

abbrev CharTwoMatrix := Matrix (Fin 2) (Fin 2) (ZMod 2)

def charTwoProjection : CharTwoMatrix := !![1, 0; 0, 0]

theorem charTwoProjection_idempotent : IsIdempotentElem charTwoProjection := by
  change charTwoProjection * charTwoProjection = charTwoProjection
  decide

/-- The characteristic-two projection still fails to commute with a directed corner. -/
theorem charTwoProjection_noncommute :
    ¬ Commute charTwoProjection (!![0, 1; 0, 0] : CharTwoMatrix) := by
  change charTwoProjection * !![0, 1; 0, 0] ≠ !![0, 1; 0, 0] * charTwoProjection
  decide

/-- Both reflection eigenspaces contain the nonzero identity in characteristic
two, but the genuine odd Peirce submodule does not. -/
theorem charTwo_eigenspaces_overlap :
    (1 : CharTwoMatrix) ∈ (conjugation charTwoProjection).eigenspace 1 ∧
    (1 : CharTwoMatrix) ∈ (conjugation charTwoProjection).eigenspace (-1) ∧
    (1 : CharTwoMatrix) ∉ LinearMap.range (odd charTwoProjection) ∧
    (1 : CharTwoMatrix) ≠ 0 := by
  have hg : reflection charTwoProjection = 1 := by decide
  refine ⟨?_, ?_, ?_, by decide⟩
  · rw [Module.End.mem_eigenspace_iff, conjugation_apply, hg]
    simp
  · rw [Module.End.mem_eigenspace_iff, conjugation_apply, hg]
    decide
  · rw [mem_odd_iff charTwoProjection_idempotent]
    decide

abbrev RationalMatrix := Matrix (Fin 2) (Fin 2) ℚ

def oblique : RationalMatrix := !![1, 1; 0, 0]
def obliqueInverse : RationalMatrix := !![1/2, 0; 1/2, 0]

/-- The concrete oblique operator and its Penrose inverse do not commute. -/
theorem oblique_inverse_noncommute :
    oblique * obliqueInverse ≠ obliqueInverse * oblique := by
  intro h
  have hh := congrArg (fun a : RationalMatrix => a 0 1) h
  norm_num [oblique, obliqueInverse, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- A genuine Penrose pair whose support difference is not tripotent. -/
theorem mp_difference_not_tripotent :
    IsMoorePenroseInverse oblique obliqueInverse ∧
    (obliqueInverse * oblique - oblique * obliqueInverse)^3 ≠
      obliqueInverse * oblique - oblique * obliqueInverse := by
  norm_num [IsMoorePenroseInverse, oblique, obliqueInverse, pow_succ,
    Matrix.star_eq_conjTranspose, Matrix.ext_iff, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Fin.forall_fin_two]
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> rfl
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The joint Drazin/Penrose hypotheses are realized with a nonzero anomaly. -/
theorem joint_hypotheses_nontrivial :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse oblique oblique 1 ∧
    IsMoorePenroseInverse oblique obliqueInverse ∧
    ⁅oblique, oblique * obliqueInverse⁆ ≠ 0 := by
  refine ⟨?_, mp_difference_not_tripotent.1, ?_⟩
  · apply InfoGeometry.Canonical.Drazin.IsDrazinInverse.of_idempotent
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    change oblique * (oblique * obliqueInverse) - (oblique * obliqueInverse) * oblique = 0 at h
    have hh := congrArg (fun a : RationalMatrix => a 0 1) h
    norm_num [oblique, obliqueInverse, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- The corrected square-zero Penrose hypotheses have a nonzero realization. -/
theorem nonzero_square_zero_mp_pair :
    let d : RationalMatrix := !![0, 1; 0, 0]
    let m : RationalMatrix := !![0, 0; 1, 0]
    d * d = 0 ∧ IsMoorePenroseInverse d m ∧ d ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j
    all_goals
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.conjTranspose_apply]
  · intro h
    have hh := congrArg (fun a : RationalMatrix => a 0 1) h
    norm_num at hh

/-- Native operator realization on `V × V`, with no finite-dimensional assumption.
Taking `V = ℕ → ℚ` gives an infinite-dimensional example. -/
theorem endomorphism_reflexive_pair {V : Type*} [AddCommGroup V] [Module ℚ V] :
    let d : Module.End ℚ (V × V) := (LinearMap.inl ℚ V V).comp (LinearMap.snd ℚ V V)
    let b : Module.End ℚ (V × V) := (LinearMap.inr ℚ V V).comp (LinearMap.fst ℚ V V)
    d * d = 0 ∧ d * b * d = d ∧ b * d * b = b := by
  dsimp only
  constructor
  · ext x <;> rfl
  constructor <;> ext x <;> rfl

end InfoGeometry.Core.NilpotentCartanRegression
