/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NeutralDualPairSplitting
import InfoGeometry.Canonical.AttentionInformationGeometry
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Query-key evaluation, logit reversal, and normalization

Queries and genuine dual keys embed in the two coordinate-null subspaces of
the existing real neutral phase space. Their cross-pairing is evaluation.
The negative para-involution changes the sign of the query and fixes the key;
it does not exchange these roles.

For finite coordinate arrays, exchanging query and key families transposes
the rectangular logit matrix. Row normalization under transpose becomes
column normalization, rather than transposing the original row-normalized
matrix. A symmetric rank-one logit matrix witnesses the distinction and
produces a rank-two softmax matrix.

No physical CPT transformation, planar graph structure, Poisson bracket,
or transformer trajectory is asserted.
-/

noncomputable section

namespace InfoGeometry.Attention.QueryKeyReversal

open Matrix
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.NeutralDualPairSplitting
open AttentionInformationGeometry
open scoped BigOperators

section DualEvaluation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The sign mirror preserves the query sector and negates its coordinate. -/
@[simp] theorem negative_para_primalIncl (q : E) :
    (-neutralParaInvolution) (primalIncl q) = primalIncl (-q) := by
  simp [neutralParaInvolution_apply]

/-- The sign mirror fixes every pure key. -/
@[simp] theorem negative_para_dualIncl (k : Module.Dual ℝ E) :
    (-neutralParaInvolution) (dualIncl k) = dualIncl k := by
  simp [neutralParaInvolution_apply]

/-- A nonzero pure query cannot be exchanged with any pure key by this mirror. -/
theorem negative_para_primalIncl_ne_dualIncl (q : E) (hq : q ≠ 0)
    (k : Module.Dual ℝ E) :
    (-neutralParaInvolution) (primalIncl q) ≠ dualIncl k := by
  intro h
  have hx : -q = 0 := by
    simpa [neutralParaInvolution_apply] using
      congrArg Prod.fst h
  exact hq (neg_eq_zero.mp hx)

end DualEvaluation

section CoordinateLogits

variable {N M D : ℕ}

/-- Unscaled finite query-key logits; temperature acts on these logits separately. -/
def queryKeyLogits (Q : Matrix (Fin N) (Fin D) ℝ)
    (K : Matrix (Fin M) (Fin D) ℝ) : Matrix (Fin N) (Fin M) ℝ :=
  Q * Kᵀ

/-- The coordinate matrix entry is the canonical neutral evaluation pairing. -/
theorem queryKeyLogits_eq_neutral (Q : Matrix (Fin N) (Fin D) ℝ)
    (K : Matrix (Fin M) (Fin D) ℝ) (i : Fin N) (j : Fin M) :
    queryKeyLogits Q K i j =
      canonicalNeutralBilin (primalIncl (Q i))
        (dualIncl (dotProductEquiv ℝ (Fin D) (K j))) := by
  rw [primalIncl_dualIncl_eta]
  change dotProduct (Q i) (K j) = dotProduct (K j) (Q i)
  exact dotProduct_comm _ _

/-- Exchanging the two input families transposes their rectangular logits. -/
theorem queryKeyLogits_transpose (Q : Matrix (Fin N) (Fin D) ℝ)
    (K : Matrix (Fin M) (Fin D) ℝ) :
    (queryKeyLogits Q K)ᵀ = queryKeyLogits K Q := by
  simp only [queryKeyLogits, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The latent dimension bounds logit rank before nonlinear normalization. -/
theorem queryKeyLogits_rank_le (Q : Matrix (Fin N) (Fin D) ℝ)
    (K : Matrix (Fin M) (Fin D) ℝ) :
    (queryKeyLogits Q K).rank ≤ D := by
  exact (Matrix.rank_mul_le_left Q Kᵀ).trans (Matrix.rank_le_width Q)

end CoordinateLogits

section Normalization

variable {N M : ℕ}

/-- Row softmax using the existing finite logit-probability owner. -/
def rowSoftmax (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => softmaxProb (S i) j

/-- Column softmax uses the same owner on each column. -/
def columnSoftmax (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => softmaxProb (fun k : Fin N => S k j) i

/-- Transposition exchanges row and column normalization. -/
theorem rowSoftmax_transpose (S : Matrix (Fin N) (Fin M) ℝ) :
    rowSoftmax Sᵀ = (columnSoftmax S)ᵀ := by
  rfl

theorem rowSoftmax_sum_one [NeZero M]
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    ∑ j : Fin M, rowSoftmax S i j = 1 :=
  softmaxProb_sum (S i)

theorem rowSoftmax_pos [NeZero M]
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < rowSoftmax S i j :=
  softmaxProb_pos (S i) j

end Normalization

/-! ## Symmetric rank-one scores with asymmetric full-rank probabilities -/

def symmetricRankOneScores : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, 1]

def symmetricRankOneFactor : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i _ => if i = 0 then 0 else 1

theorem symmetricRankOneScores_factorization :
    symmetricRankOneScores =
      queryKeyLogits symmetricRankOneFactor symmetricRankOneFactor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricRankOneScores, queryKeyLogits, symmetricRankOneFactor,
      Matrix.mul_apply, Fin.sum_univ_one]

theorem symmetricRankOneScores_rank_le_one :
    symmetricRankOneScores.rank ≤ 1 := by
  rw [symmetricRankOneScores_factorization]
  exact queryKeyLogits_rank_le _ _

@[simp] theorem symmetricRankOneScores_transpose :
    symmetricRankOneScoresᵀ = symmetricRankOneScores := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rowSoftmax_symmetricRankOneScores_zero_zero :
    rowSoftmax symmetricRankOneScores 0 0 = 1 / 2 := by
  norm_num [rowSoftmax, softmaxProb, partitionZ, symmetricRankOneScores,
    Fin.sum_univ_two]

theorem rowSoftmax_symmetricRankOneScores_zero_one :
    rowSoftmax symmetricRankOneScores 0 1 = 1 / 2 := by
  norm_num [rowSoftmax, softmaxProb, partitionZ, symmetricRankOneScores,
    Fin.sum_univ_two]

theorem rowSoftmax_symmetricRankOneScores_one_zero :
    rowSoftmax symmetricRankOneScores 1 0 = 1 / (1 + Real.exp 1) := by
  norm_num [rowSoftmax, softmaxProb, partitionZ, symmetricRankOneScores,
    Fin.sum_univ_two]

theorem rowSoftmax_symmetricRankOneScores_one_one :
    rowSoftmax symmetricRankOneScores 1 1 = Real.exp 1 / (1 + Real.exp 1) := by
  norm_num [rowSoftmax, softmaxProb, partitionZ, symmetricRankOneScores,
    Fin.sum_univ_two]

/-- Symmetric logits need not have symmetric row-normalized probabilities. -/
theorem rowSoftmax_symmetricRankOneScores_not_symmetric :
    (rowSoftmax symmetricRankOneScores)ᵀ ≠
      rowSoftmax symmetricRankOneScores := by
  intro h
  have heq := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  change rowSoftmax symmetricRankOneScores 1 0 =
    rowSoftmax symmetricRankOneScores 0 1 at heq
  rw [rowSoftmax_symmetricRankOneScores_one_zero,
    rowSoftmax_symmetricRankOneScores_zero_one] at heq
  have hpos : 0 < 1 + Real.exp 1 := by positivity
  have hmul := (div_eq_iff (ne_of_gt hpos)).mp heq
  have hexp : 1 < Real.exp (1 : ℝ) :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  nlinarith

/-- A concrete failure of the proposed row-softmax/transpose commutation. -/
theorem rowSoftmax_transpose_counterexample :
    rowSoftmax symmetricRankOneScoresᵀ ≠
      (rowSoftmax symmetricRankOneScores)ᵀ := by
  rw [symmetricRankOneScores_transpose]
  exact Ne.symm rowSoftmax_symmetricRankOneScores_not_symmetric

theorem rowSoftmax_symmetricRankOneScores_det :
    (rowSoftmax symmetricRankOneScores).det =
      (Real.exp 1 - 1) / (2 * (1 + Real.exp 1)) := by
  rw [Matrix.det_fin_two, rowSoftmax_symmetricRankOneScores_zero_zero,
    rowSoftmax_symmetricRankOneScores_one_one,
    rowSoftmax_symmetricRankOneScores_zero_one,
    rowSoftmax_symmetricRankOneScores_one_zero]
  have hne : 1 + Real.exp (1 : ℝ) ≠ 0 := by positivity
  field_simp [hne] <;> ring

theorem rowSoftmax_symmetricRankOneScores_det_pos :
    0 < (rowSoftmax symmetricRankOneScores).det := by
  rw [rowSoftmax_symmetricRankOneScores_det]
  apply div_pos
  · exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by norm_num))
  · positivity

/-- Nonlinear row normalization can raise the latent rank bound. -/
theorem rowSoftmax_symmetricRankOneScores_rank_two :
    (rowSoftmax symmetricRankOneScores).rank = 2 := by
  simpa using Matrix.rank_of_det_ne_zero
    (ne_of_gt rowSoftmax_symmetricRankOneScores_det_pos)

end InfoGeometry.Attention.QueryKeyReversal
