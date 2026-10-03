import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

import InfoGeometry.Probability.DetectorFoundationalCopula

open Matrix
open scoped BigOperators

namespace InfoGeometry.Canonical.AttentionGlauberCopulaBridge

open InfoGeometry.Probability.DetectorFoundationalCopula

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### 1. Attention Matrix & Softmax Normalization -/

/-- Row partition sum Z(i) = ∑_j exp(S_{i, j}). -/
noncomputable def partitionZ (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin M, Real.exp (S i j)

omit [NeZero N] in
/-- The partition function is strictly positive because exp > 0. -/
lemma partitionZ_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    0 < partitionZ S i := by
  dsimp [partitionZ]
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos (S i j)
  · exact Finset.univ_nonempty

/-- The Softmax Attention matrix A_{i, j} = exp(S_{i, j}) / Z(i). -/
noncomputable def attentionMatrix (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => Real.exp (S i j) / partitionZ S i

/-- Each row of the attention matrix sums to 1. -/
theorem attention_row_sum (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    (∑ j : Fin M, attentionMatrix S i j) = 1 := by
  dsimp [attentionMatrix]
  rw [← Finset.sum_div]
  have hZ : partitionZ S i ≠ 0 := ne_of_gt (partitionZ_pos S i)
  exact div_self hZ

/-- Attention weights are strictly positive. -/
theorem attention_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < attentionMatrix S i j :=
  div_pos (Real.exp_pos (S i j)) (partitionZ_pos S i)

/-! ### 2. Normalized Bipartite Joint Distribution -/

/-- Normalized joint probability P(i, j) = (1 / N) * A_{i, j}. -/
noncomputable def jointDistribution (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => (1 / (N : ℝ)) * attentionMatrix S i j

/-- Every entry of the finite joint law is strictly positive. -/
theorem jointDistribution_pos (S : Matrix (Fin N) (Fin M) ℝ)
    (i : Fin N) (j : Fin M) :
    0 < jointDistribution S i j := by
  dsimp [jointDistribution]
  have hN : 0 < (1 / (N : ℝ)) :=
    one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  exact mul_pos hN (attention_pos S i j)

/-- The joint distribution sums to 1 across the bipartite space Fin N × Fin M. -/
theorem joint_total_sum (S : Matrix (Fin N) (Fin M) ℝ) :
    (∑ i : Fin N, ∑ j : Fin M, jointDistribution S i j) = 1 := by
  dsimp [jointDistribution]
  have h_inner : ∀ i : Fin N, (∑ j : Fin M, (1 / (N : ℝ)) * attentionMatrix S i j) =
      (1 / (N : ℝ)) := by
    intro i
    rw [← Finset.mul_sum, attention_row_sum S i, mul_one]
  simp_rw [h_inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact nsmul_eq_mul (N : ℕ) (1 / (N : ℝ)) ▸ mul_one_div_cancel hN

/-- Query marginal distribution p(i) = ∑_j P(i, j) = 1 / N. -/
noncomputable def rowMarginal (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin M, jointDistribution S i j

theorem rowMarginal_eq_uniform (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    rowMarginal S i = 1 / (N : ℝ) := by
  dsimp [rowMarginal, jointDistribution]
  rw [← Finset.mul_sum, attention_row_sum S i, mul_one]

/-- Key marginal distribution q(j) = ∑_i P(i, j). -/
noncomputable def colMarginal (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  ∑ i : Fin N, jointDistribution S i j

/-- Every key marginal is strictly positive because the query type is
nonempty and every joint mass is positive. -/
theorem colMarginal_pos (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) :
    0 < colMarginal S j := by
  dsimp [colMarginal]
  apply Finset.sum_pos
  · intro i _
    exact jointDistribution_pos S i j
  · exact Finset.univ_nonempty

theorem colMarginal_ne_zero (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) :
    colMarginal S j ≠ 0 := ne_of_gt (colMarginal_pos S j)

/-- The key marginal sums to 1. -/
theorem colMarginal_sum (S : Matrix (Fin N) (Fin M) ℝ) :
    (∑ j : Fin M, colMarginal S j) = 1 := by
  dsimp [colMarginal]
  rw [Finset.sum_comm]
  exact joint_total_sum S

/-! ### 3. Marginal-normalized attention weights -/

/-- A finite probability ratio derived from the attention weights. This is not
a quantum-optics Glauber correlator. -/
noncomputable def attentionDependenceRatio
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) : ℝ :=
  jointDistribution S i j / (rowMarginal S i * colMarginal S j)

/- The ratio reduces to an attention weight divided by its column marginal. -/
theorem attentionDependenceRatio_eq_weight_div_colMarginal
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    attentionDependenceRatio S i j = attentionMatrix S i j / colMarginal S j := by
  dsimp [attentionDependenceRatio, jointDistribution]
  rw [rowMarginal_eq_uniform S i]
  have hN : (1 / (N : ℝ)) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have h_alg : ((1 / (N : ℝ)) * attentionMatrix S i j) / ((1 / (N : ℝ)) * colMarginal S j) =
      attentionMatrix S i j / colMarginal S j := by
    rw [mul_div_mul_left (attentionMatrix S i j) (colMarginal S j) hN]
  exact h_alg

/-- The marginal-normalized attention ratio is strictly positive. -/
theorem attentionDependenceRatio_pos
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < attentionDependenceRatio S i j := by
  rw [attentionDependenceRatio_eq_weight_div_colMarginal]
  exact div_pos (attention_pos S i j) (colMarginal_pos S j)

/-! ### 4. Shannon information for the finite attention law -/

/-- Shannon entropy of the key marginal. -/
noncomputable def keyEntropy (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  - ∑ j : Fin M, colMarginal S j * Real.log (colMarginal S j)

/-- Conditional entropy of the key given a query, using the softmax row as the
conditional key law. -/
noncomputable def conditionalKeyEntropy (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  - ∑ i : Fin N, ∑ j : Fin M,
    jointDistribution S i j * Real.log (attentionMatrix S i j)

/-- Shannon mutual information for this finite model, in the entropy-difference
form `H(K) - H(K | Q)`. -/
noncomputable def attentionMutualInformation
    (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  keyEntropy S - conditionalKeyEntropy S

/-- Expected log of the marginal-normalized attention ratio under the joint
law. -/
noncomputable def expectedLogDependenceRatio
    (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin M,
    jointDistribution S i j * Real.log (attentionDependenceRatio S i j)

/-- The log of the dependence ratio is the log softmax weight minus the log
key marginal. -/
theorem log_attentionDependenceRatio
    (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    Real.log (attentionDependenceRatio S i j) =
      Real.log (attentionMatrix S i j) - Real.log (colMarginal S j) := by
  rw [attentionDependenceRatio_eq_weight_div_colMarginal]
  exact Real.log_div (ne_of_gt (attention_pos S i j))
    (ne_of_gt (colMarginal_pos S j))

omit [NeZero N] [NeZero M] in
/-- Finite marginal contraction for the logarithm of the key marginal. -/
theorem sum_joint_mul_log_colMarginal
    (S : Matrix (Fin N) (Fin M) ℝ) :
    (∑ i : Fin N, ∑ j : Fin M,
      jointDistribution S i j * Real.log (colMarginal S j)) =
      ∑ j : Fin M, colMarginal S j * Real.log (colMarginal S j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  rfl

/-- The expected log dependence ratio equals Shannon mutual information. -/
theorem attentionMutualInformation_eq_expectedLogDependenceRatio
    (S : Matrix (Fin N) (Fin M) ℝ) :
    attentionMutualInformation S = expectedLogDependenceRatio S := by
  unfold attentionMutualInformation expectedLogDependenceRatio
  simp_rw [log_attentionDependenceRatio, mul_sub, Finset.sum_sub_distrib]
  rw [sum_joint_mul_log_colMarginal]
  unfold keyEntropy conditionalKeyEntropy
  ring

/-- Query-independent attention has dependence ratio one at every pair. -/
theorem attentionDependenceRatio_eq_one_of_query_independent
    (S : Matrix (Fin N) (Fin M) ℝ)
    (h : ∀ i j, attentionMatrix S i j = colMarginal S j)
    (i : Fin N) (j : Fin M) :
    attentionDependenceRatio S i j = 1 := by
  rw [attentionDependenceRatio_eq_weight_div_colMarginal, h i j]
  exact div_self (ne_of_gt (colMarginal_pos S j))

/-- Query-independent attention has zero mutual information in the finite
model. -/
theorem attentionMutualInformation_eq_zero_of_query_independent
    (S : Matrix (Fin N) (Fin M) ℝ)
    (h : ∀ i j, attentionMatrix S i j = colMarginal S j) :
    attentionMutualInformation S = 0 := by
  rw [attentionMutualInformation_eq_expectedLogDependenceRatio]
  unfold expectedLogDependenceRatio
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [attentionDependenceRatio_eq_one_of_query_independent S h i j]
  simp

/-! ### 4. Finite cumulative tables -/

/-- Joint cumulative distribution function (CDF) H(i, j) = ∑_{a ≤ i, b ≤ j} P(a, b). -/
noncomputable def jointCDF (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) : ℝ :=
  ∑ a : Fin N, ∑ b : Fin M, if a ≤ i ∧ b ≤ j then jointDistribution S a b else 0

/-- Row marginal CDF F(i) = ∑_{a ≤ i} p(a). -/
noncomputable def rowCDF (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ a : Fin N, if a ≤ i then rowMarginal S a else 0

/-- Column marginal CDF G(j) = ∑_{b ≤ j} q(b). -/
noncomputable def colCDF (S : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  ∑ b : Fin M, if b ≤ j then colMarginal S b else 0

/-! ### 5. Query-independent attention and independence -/

/- If every query row equals the key marginal, the finite joint CDF factors as
the product of its marginal CDFs. This is an independence result for this
finite probability model, not an identity with a quantum-optics correlator. -/
theorem query_independent_attention_cdf_factorization
    (S : Matrix (Fin N) (Fin M) ℝ)
    (h_unentangled : ∀ (i : Fin N) (j : Fin M), attentionMatrix S i j = colMarginal S j)
    (i : Fin N) (j : Fin M) :
    jointCDF S i j =
      InfoGeometry.Probability.DetectorFoundationalCopula.productCopula
        (rowCDF S i) (colCDF S j) := by
  dsimp [jointCDF, rowCDF, colCDF,
    InfoGeometry.Probability.DetectorFoundationalCopula.productCopula,
    rowMarginal, colMarginal, jointDistribution]
  have h_fact : ∀ a b, (if a ≤ i ∧ b ≤ j then (1 / (N : ℝ)) * attentionMatrix S a b else 0) =
      (if a ≤ i then (1 / (N : ℝ)) else 0) * (if b ≤ j then colMarginal S b else 0) := by
    intro a b
    by_cases ha : a ≤ i <;> by_cases hb : b ≤ j
    · simp only [ha, hb, and_self, if_true]
      rw [h_unentangled a b]
    · simp only [hb, and_false, if_false, mul_zero]
    · simp only [ha, false_and, if_false, zero_mul]
    · simp only [ha, false_and, if_false, zero_mul]

  simp_rw [h_fact]
  rw [← Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · exact (rowMarginal_eq_uniform S a).symm
  · rfl

end InfoGeometry.Canonical.AttentionGlauberCopulaBridge
