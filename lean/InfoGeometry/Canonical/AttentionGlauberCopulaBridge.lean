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
