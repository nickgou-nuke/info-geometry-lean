import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option linter.unusedSectionVars false

open Matrix
open scoped BigOperators

namespace AttentionEntropyDecomposition

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### 1. Attention Matrix & Probability Distribution -/

noncomputable def partitionZ (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin M, Real.exp (S i j)

lemma partitionZ_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    0 < partitionZ S i := by
  dsimp [partitionZ]
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos (S i j)
  · exact Finset.univ_nonempty

noncomputable def attentionMatrix (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => Real.exp (S i j) / partitionZ S i

theorem attention_row_sum (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    (∑ j : Fin M, attentionMatrix S i j) = 1 := by
  dsimp [attentionMatrix]
  rw [← Finset.sum_div]
  have hZ : partitionZ S i ≠ 0 := ne_of_gt (partitionZ_pos S i)
  exact div_self hZ

theorem attention_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < attentionMatrix S i j :=
  div_pos (Real.exp_pos (S i j)) (partitionZ_pos S i)

noncomputable def jointDistribution (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => (1 / (N : ℝ)) * attentionMatrix S i j

theorem jointDistribution_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < jointDistribution S i j := by
  dsimp [jointDistribution]
  have hN : 0 < (1 / (N : ℝ)) := one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  exact mul_pos hN (attention_pos S i j)

noncomputable def rowMarginal (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin M, jointDistribution S i j

theorem rowMarginal_eq_uniform (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    rowMarginal S i = 1 / (N : ℝ) := by
  dsimp [rowMarginal, jointDistribution]
  rw [← Finset.mul_sum, attention_row_sum S i, mul_one]

noncomputable def colMarginal (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  ∑ i : Fin N, jointDistribution S i j

theorem colMarginal_pos (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) :
    0 < colMarginal S j := by
  dsimp [colMarginal]
  apply Finset.sum_pos
  · intro i _
    exact jointDistribution_pos S i j
  · exact Finset.univ_nonempty

theorem colMarginal_ne_zero (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) :
    colMarginal S j ≠ 0 :=
  ne_of_gt (colMarginal_pos S j)

/-! ### 2. Entropic Quantities -/

noncomputable def entropyKey (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  - ∑ j : Fin M, colMarginal S j * Real.log (colMarginal S j)

noncomputable def conditionalEntropyAt (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  - ∑ j : Fin M, attentionMatrix S i j * Real.log (attentionMatrix S i j)

noncomputable def conditionalEntropy (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  - ∑ i : Fin N, ∑ j : Fin M, jointDistribution S i j * Real.log (attentionMatrix S i j)

noncomputable def mutualInformation (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin M,
    jointDistribution S i j * Real.log (jointDistribution S i j / (rowMarginal S i * colMarginal S j))

/-! ### 3. Structural Lemmas -/

theorem conditionalEntropy_eq_expected (S : Matrix (Fin N) (Fin M) ℝ) :
    conditionalEntropy S = ∑ i : Fin N, rowMarginal S i * conditionalEntropyAt S i := by
  dsimp [conditionalEntropy, conditionalEntropyAt, jointDistribution]
  simp_rw [rowMarginal_eq_uniform S]
  have h_inner : ∀ i : Fin N,
      (∑ j : Fin M, (1 / (N : ℝ)) * attentionMatrix S i j * Real.log (attentionMatrix S i j)) =
        (1 / (N : ℝ)) * (∑ j : Fin M, attentionMatrix S i j * Real.log (attentionMatrix S i j)) := by
    intro i
    have h_assoc : ∀ j, (1 / (N : ℝ)) * attentionMatrix S i j * Real.log (attentionMatrix S i j) =
      (1 / (N : ℝ)) * (attentionMatrix S i j * Real.log (attentionMatrix S i j)) := by intro j; ring
    simp_rw [h_assoc]
    rw [← Finset.mul_sum]
  simp_rw [h_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma joint_div_marginal_eq (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    jointDistribution S i j / (rowMarginal S i * colMarginal S j) =
      attentionMatrix S i j / colMarginal S j := by
  dsimp [jointDistribution]
  rw [rowMarginal_eq_uniform S i]
  have hN : (1 / (N : ℝ)) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))
  exact mul_div_mul_left (attentionMatrix S i j) (colMarginal S j) hN

lemma log_ratio_eq (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    Real.log (jointDistribution S i j / (rowMarginal S i * colMarginal S j)) =
      Real.log (attentionMatrix S i j) - Real.log (colMarginal S j) := by
  rw [joint_div_marginal_eq S i j]
  have hA : attentionMatrix S i j ≠ 0 := ne_of_gt (attention_pos S i j)
  have hq : colMarginal S j ≠ 0 := colMarginal_ne_zero S j
  exact Real.log_div hA hq

lemma sum_joint_mul_log_colMarginal (S : Matrix (Fin N) (Fin M) ℝ) :
    (∑ i : Fin N, ∑ j : Fin M, jointDistribution S i j * Real.log (colMarginal S j)) =
      ∑ j : Fin M, colMarginal S j * Real.log (colMarginal S j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  rfl

/-! ### 4. The Shannon Entropy Decomposition Theorem -/

theorem mutualInformation_eq_entropyKey_sub_conditionalEntropy
    (S : Matrix (Fin N) (Fin M) ℝ) :
    mutualInformation S = entropyKey S - conditionalEntropy S := by
  dsimp [mutualInformation, entropyKey, conditionalEntropy]
  have h_summand : ∀ (i : Fin N) (j : Fin M),
      jointDistribution S i j * Real.log (jointDistribution S i j / (rowMarginal S i * colMarginal S j)) =
        jointDistribution S i j * Real.log (attentionMatrix S i j) -
        jointDistribution S i j * Real.log (colMarginal S j) := by
    intro i j
    rw [log_ratio_eq S i j]
    ring
  simp_rw [h_summand]
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_joint_mul_log_colMarginal S]
  ring

/-! ### 5. Unentangled Coherent Limit -/

theorem unentangled_conditionalEntropy_eq_entropyKey
    (S : Matrix (Fin N) (Fin M) ℝ)
    (h_unentangled : ∀ (i : Fin N) (j : Fin M), attentionMatrix S i j = colMarginal S j) :
    conditionalEntropy S = entropyKey S := by
  dsimp [conditionalEntropy, entropyKey, jointDistribution]
  simp_rw [h_unentangled]
  have h_neg : - (∑ i : Fin N, ∑ j : Fin M, (1 / (N : ℝ)) * colMarginal S j * Real.log (colMarginal S j)) =
    - ∑ j : Fin M, colMarginal S j * Real.log (colMarginal S j) := by
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have h_pull : (∑ i : Fin N, (1 / (N : ℝ)) * colMarginal S j * Real.log (colMarginal S j)) =
        (∑ i : Fin N, (1 / (N : ℝ))) * (colMarginal S j * Real.log (colMarginal S j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_pull]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [nsmul_eq_mul (N : ℕ) (1 / (N : ℝ)), mul_one_div_cancel hN, one_mul]
  exact h_neg

theorem unentangled_mutualInformation_zero_via_entropy
    (S : Matrix (Fin N) (Fin M) ℝ)
    (h_unentangled : ∀ (i : Fin N) (j : Fin M), attentionMatrix S i j = colMarginal S j) :
    mutualInformation S = 0 := by
  rw [mutualInformation_eq_entropyKey_sub_conditionalEntropy]
  rw [unentangled_conditionalEntropy_eq_entropyKey S h_unentangled]
  ring

end AttentionEntropyDecomposition
