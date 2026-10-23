/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport

/-!
# A concrete Markov--Majorana noncommutation witness

This finite example uses the repository's row-softmax constructor and its
Jordan--Wigner creation/annihilation matrices on the same full `2 × 2` matrix
algebra. For uniform two-state logits, the Markov Laplacian has a concrete
group inverse. Its range involution anticommutes with the repository's
Majorana difference, so these two axes do not automatically commute.

The positive resolution is in `MarkovMajoranaCliffordResolution`: these same
axes define a surjective representation of the native split Clifford algebra,
with an explicit reconstruction of every matrix. Noncommutation is thus a
boundary against the commuting-axis formulation, not the final construction.

This file proves a finite matrix obstruction only. It does not identify tokens
with physical particles, establish a sink potential, or prove any disk,
continuum, stability, or density-wave claim.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction

open Matrix
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext

abbrev Operator := Matrix (Fin 2) (Fin 2) ℝ

/-- Uniform scores on the two-state carrier. -/
def uniformScores (_i _j : Fin 2) : ℝ := 0

/-- The actual row-softmax transition matrix for `uniformScores`. -/
def uniformTransition : Operator := softmaxAttentionMatrix uniformScores

@[simp] theorem uniformTransition_apply (i j : Fin 2) :
    uniformTransition i j = (1 : ℝ) / 2 := by
  simp [uniformTransition, uniformScores, softmaxAttentionMatrix,
    softmaxAttentionKernel, queryPartitionFunction, gibbsCouplingWeight,
    Fin.sum_univ_two, Real.exp_zero]

/-- The Markov Laplacian at the uniform softmax point. -/
def uniformLaplacian : Operator := 1 - uniformTransition

/-- The displayed group inverse is the same full matrix operator at this
idempotent Laplacian. -/
def uniformGroupInverse : Operator := uniformLaplacian

theorem uniformLaplacian_idempotent :
    uniformLaplacian * uniformLaplacian = uniformLaplacian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformLaplacian, uniformTransition_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

/-- A genuine group inverse certificate for `I - P` in the nontrivial matrix
algebra, proved from the explicit softmax entries. -/
theorem uniformGroupInverse_spec :
    IsGroupInverse uniformLaplacian uniformGroupInverse := by
  unfold IsGroupInverse uniformGroupInverse
  have hsq := uniformLaplacian_idempotent
  constructor
  · calc
      uniformLaplacian * uniformLaplacian * uniformLaplacian =
          uniformLaplacian * uniformLaplacian := by
            exact congrArg (fun X : Operator => X * uniformLaplacian) hsq
      _ = uniformLaplacian := hsq
  constructor
  · calc
      uniformLaplacian * uniformLaplacian * uniformLaplacian =
          uniformLaplacian * uniformLaplacian := by
            exact congrArg (fun X : Operator => X * uniformLaplacian) hsq
      _ = uniformLaplacian := hsq
  · rfl

/-- The range involution `(2E - I)` determined by the Markov group inverse. -/
def rangeInvolution : Operator :=
  (2 : ℝ) • markovRangeIdempotent uniformTransition uniformGroupInverse - 1

/-- The actual repository Jordan--Wigner Majorana direction on the base
two-dimensional matrix carrier. -/
def firstMajorana : Operator := a_dagger_base - a_base

theorem rangeInvolution_explicit :
    rangeInvolution = !![(0 : ℝ), -1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rangeInvolution, markovRangeIdempotent, uniformGroupInverse,
      uniformLaplacian, uniformTransition_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]

theorem firstMajorana_explicit :
    firstMajorana = !![(0 : ℝ), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstMajorana, a_dagger_base, a_base]

/-- The Markov range involution anticommutes with a source-defined Majorana
operator; in particular, it fails to commute with that operator. -/
theorem rangeInvolution_majorana_anticommute :
    rangeInvolution * firstMajorana = -(firstMajorana * rangeInvolution) := by
  rw [rangeInvolution_explicit, firstMajorana_explicit]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem rangeInvolution_majorana_noncommute :
    rangeInvolution * firstMajorana ≠ firstMajorana * rangeInvolution := by
  rw [rangeInvolution_explicit, firstMajorana_explicit]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction
