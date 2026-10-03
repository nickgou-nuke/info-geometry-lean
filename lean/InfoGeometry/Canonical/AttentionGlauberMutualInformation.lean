import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace AttentionGlauberCopula

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### 1. Softmax Attention and Joint Distribution -/

/-- Row partition sum Z(i) = ∑_j exp(S_{i, j}). -/
noncomputable def partitionZ (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) : ℝ :=
  ∑ j : Fin M, Real.exp (S i j)

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

theorem attention_row_sum (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) :
    (∑ j : Fin M, attentionMatrix S i j) = 1 := by
  dsimp [attentionMatrix]
  rw [← Finset.sum_div]
  have hZ : partitionZ S i ≠ 0 := ne_of_gt (partitionZ_pos S i)
  exact div_self hZ

theorem attention_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < attentionMatrix S i j :=
  div_pos (Real.exp_pos (S i j)) (partitionZ_pos S i)

/-- Normalized joint probability P(i, j) = (1 / N) * A_{i, j}. -/
noncomputable def jointDistribution (S : Matrix (Fin N) (Fin M) ℝ) :
    Matrix (Fin N) (Fin M) ℝ :=
  fun i j => (1 / (N : ℝ)) * attentionMatrix S i j

theorem jointDistribution_pos (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) :
    0 < jointDistribution S i j := by
  dsimp [jointDistribution]
  have hN : 0 < (1 / (N : ℝ)) := by
    refine one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  exact mul_pos hN (attention_pos S i j)

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

/-! ### 2. The Glauber 2-Point Cross-Correlator -/

/-- The Glauber 2-point cross-correlator g^(2)(i, j) = P(i, j) / (p(i) * q(j)). -/
noncomputable def glauberCorrelator (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M) : ℝ :=
  jointDistribution S i j / (rowMarginal S i * colMarginal S j)

/-- The Glauber correlator is identically the normalized attention ratio A_{i, j} / q(j). -/
theorem glauber_correlator_eq_attention_ratio (S : Matrix (Fin N) (Fin M) ℝ) (i : Fin N) (j : Fin M)
    (hq : colMarginal S j ≠ 0) :
    glauberCorrelator S i j = attentionMatrix S i j / colMarginal S j := by
  dsimp [glauberCorrelator, jointDistribution]
  rw [rowMarginal_eq_uniform S i]
  have hN : (1 / (N : ℝ)) ≠ 0 := one_div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))
  exact mul_div_mul_left (attentionMatrix S i j) (colMarginal S j) hN

/-! ### 3. Discrete Mutual Information & Core Theorem -/

/-- Discrete Shannon Mutual Information I(Q; K) = ∑_{i, j} P(i, j) * ln(P(i, j) / (p(i) * q(j))). -/
noncomputable def mutualInformation (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin M,
    jointDistribution S i j * Real.log (jointDistribution S i j / (rowMarginal S i * colMarginal S j))

/-- Expected Log-Glauber Correlator: E_P[ln g^(2)(Q, K)] = ∑_{i, j} P(i, j) * ln(g^(2)(i, j)). -/
noncomputable def expectedLogGlauber (S : Matrix (Fin N) (Fin M) ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin M,
    jointDistribution S i j * Real.log (glauberCorrelator S i j)

/-- Fundamental Theorem: Mutual Information between Query and Key
    is identically the expected Log-Glauber Correlator. -/
theorem mutualInformation_eq_sum_glauber (S : Matrix (Fin N) (Fin M) ℝ) :
    mutualInformation S = expectedLogGlauber S := by
  dsimp [mutualInformation, expectedLogGlauber, glauberCorrelator]

/-! ### 4. Coherent State Invariance (Vanishing Mutual Information) -/

/-- For unentangled attention (A_{i, j} = q(j)), the Glauber correlator is uniformly 1. -/
theorem unentangled_glauber_eq_one (S : Matrix (Fin N) (Fin M) ℝ)
    (h_unentangled : ∀ (i : Fin N) (j : Fin M), attentionMatrix S i j = colMarginal S j)
    (i : Fin N) (j : Fin M) :
    glauberCorrelator S i j = 1 := by
  rw [glauber_correlator_eq_attention_ratio S i j (colMarginal_ne_zero S j)]
  rw [h_unentangled i j]
  exact div_self (colMarginal_ne_zero S j)

/-- Coherent State Theorem:
    When the attention mechanism is unentangled (independent product copula),
    the Mutual Information vanishes identically: I(Q; K) = 0. -/
theorem unentangled_mutual_information_zero (S : Matrix (Fin N) (Fin M) ℝ)
    (h_unentangled : ∀ (i : Fin N) (j : Fin M), attentionMatrix S i j = colMarginal S j) :
    mutualInformation S = 0 := by
  rw [mutualInformation_eq_sum_glauber]
  dsimp [expectedLogGlauber]
  have h_term : ∀ (i : Fin N) (j : Fin M),
      jointDistribution S i j * Real.log (glauberCorrelator S i j) = 0 := by
    intro i j
    have hg : glauberCorrelator S i j = 1 := unentangled_glauber_eq_one S h_unentangled i j
    rw [hg, Real.log_one, mul_zero]
  have h_inner : ∀ (i : Fin N),
      (∑ j : Fin M, jointDistribution S i j * Real.log (glauberCorrelator S i j)) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro j _
    exact h_term i j
  apply Finset.sum_eq_zero
  intro i _
  exact h_inner i

end AttentionGlauberCopula
